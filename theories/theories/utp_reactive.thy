(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive.thy                                                     *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* Reactive Processes *}

theory utp_reactive
imports 
  utp_theory
  "reactive/utp_reactive_lemmas"
begin

default_sort REACTIVE_SORT

abbreviation "ref  \<equiv> MkPlainP ''ref'' True TYPE('m EVENT USET) TYPE('m)"

abbreviation "REA \<equiv> {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}"

text {* R1 ensures that the trace only gets longer *}

definition R1 :: " 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R1(P) = `P \<and> ($tr \<le> $tr\<acute>)`"

text {* R2 ensures that the trace only gets longer *}

definition R2s :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R2s(P) = `P[\<langle>\<rangle> / tr][($tr\<acute> - $tr) / tr\<acute>]`"

definition R2 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R2(P) = R1 (R2s P)"

definition R3 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R3(P) = `II \<lhd> $wait \<rhd> P`"

definition RH :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where 
"RH P = (R1 \<circ> R2 \<circ> R3)P"

declare R1_def [eval, evalr, evalrr, evalrx, evalp]
declare R2_def [eval, evalr, evalrr, evalrx, evalp]
declare R2s_def [eval, evalr, evalrr, evalrx, evalp]
declare R3_def [eval, evalr, evalrr, evalrx, evalp]
declare is_healthy_def [eval, evalr, evalrr, evalrx, evalp]
declare RH_def [eval, evalr, evalrr, evalrx, evalp]

subsection {* Closure Laws *}

lemma WF_RELATION_UNREST:
  "NON_REL_VAR \<sharp> P \<Longrightarrow> P \<in> WF_RELATION"
  by (simp add:WF_RELATION_def)

lemma R1_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R1(P) \<in> WF_RELATION"
  by (simp add:R1_def closure unrest WF_RELATION_UNREST)

lemma R2s_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R2s(P) \<in> WF_RELATION"
  by (simp add:R2s_def unrest typing defined closure)

lemma R2_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R2(P) \<in> WF_RELATION"
  by (simp add:R2_def closure)

lemma R3_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R3(P) \<in> WF_RELATION"
  by (simp add:R3_def closure)

lemma RH_rel_closure [closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> RH(P) \<in> WF_RELATION"
  by (simp add:RH_def closure)

subsection {* Sorried Laws *}

(* Trace sequence relation *)
lemma Aida : "`(($tr \<le> $tr\<acute>) ; ((\<not>ok \<and> $wait) \<and> ($tr \<le> $tr\<acute>)))`=`($tr \<le> $tr\<acute>)`"
  apply (subst SemiR_remove_middle_unrest1[of _ _ "{okay\<down>, wait\<down>}"])
  apply (simp_all add: closure typing defined unrest WF_RELATION_UNREST)
  apply (utp_pred_tac)
  apply (rule_tac x="\<B>(okay\<down> :=\<^sub>b FalseV, wait\<down> :=\<^sub>b TrueV)" in exI)
  apply (simp add:typing)
  apply (metis tr_leq_trans)
done
    
lemma Aidc : "`$wait \<and> ($wait\<acute> = $wait)` = `$wait \<and> $wait\<acute>`" by utp_poly_auto_tac

lemma tr_conserved_is_R1 : "`R1($tr\<acute> = $tr)` = `($tr\<acute> = $tr)`" by(simp add:R1_def, utp_poly_auto_tac)

lemma R1_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R1(P) \<sqsubseteq> R1(Q)" 
  by utp_pred_tac

subsection {* R1 Laws *}

(* L1 R1-idempotent *)

lemma R1_idempotent:
  "R1(R1(P)) = R1(P)"
  by (utp_rel_tac)

(* L2 R1-\<and> *)

lemma R1_AndP:
  "`R1(P \<and> Q)` = `R1(P) \<and> R1(Q)`"
  by (utp_pred_auto_tac)

(* L3 R1-\<or> *)

lemma R1_OrP:
  "`R1(P \<or> Q)` = `R1(P) \<or> R1(Q)`"
  by (utp_pred_auto_tac)
  
(* L4 R1-extend-\<and> *)

lemma R1_extend_AndP : 
  "`R1(P) \<and> Q` = `R1(P \<and> Q)`"
  by (utp_pred_auto_tac)

(* L5 R1-conditional *)

lemma R1_CondR:
  "`R1(P \<lhd> b \<rhd> Q)` = `R1(P) \<lhd> b \<rhd> R1(Q)`"
  by (utp_pred_auto_tac)

(* L6 R1-negate-R1 *)

lemma R1_negate_R1: 
  "`R1(\<not>R1(P))` = `R1(\<not>P)`"
  by(utp_pred_auto_tac)
  
(* L7 R1-wait *)

lemma R1_wait_true: 
  "(R1(P))\<^sub>t = R1(P\<^sub>t)"
by(simp add:R1_def, utp_poly_auto_tac)

lemma R1_wait_false: 
  "(R1(P))\<^sub>f = R1(P\<^sub>f)"
by(simp add:R1_def, utp_poly_auto_tac)

(* L8 II_rel-R1 *)

lemma R1_SkipR:
  "R1(II) = II"
  by (auto simp add:eval evalp closure Rep_binding_ty_def)

(* L9 II_rea-R1 *)

lemma R1_tr_leq_tr':
  "`R1($tr \<le> $tr\<acute>)` = `$tr \<le> $tr\<acute>`"
  by (simp add:R1_def)

(* L10 R1-\<and>-closure *)

lemma R1_AndP_closure: 
assumes "P is R1" "Q is R1"
shows "`(P \<and> Q)` is R1"
by (metis Healthy_intro Healthy_simp R1_extend_AndP assms(1))

(* L11 R1-\<or>-closure *)

lemma R1_OrP_closure: 
assumes "P is R1" "Q is R1"
shows "`(P \<or> Q)` is R1"
by (metis R1_OrP assms(1) assms(2) is_healthy_def)

(* L12 R1-conditional-closure *)

lemma R1_CondR_closure: 
assumes "P is R1" "Q is R1"
shows "`(P \<lhd> b \<rhd> Q)` is R1"
by (metis Healthy_intro Healthy_simp R1_CondR assms(1) assms(2))

(* L13 R10-sequence-closure *)

lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> `$tr \<le> $tr\<acute>` \<sqsubseteq> P" 
  by (utp_pred_auto_tac)

theorem R1_SemiR_closure [closure]:
  assumes
    "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
    "P is R1" "Q is R1"
  shows "(P ; Q) is R1"
  using assms
  apply (unfold R1_by_refinement)
  apply (rule order_trans)
  apply (rule SemiR_mono_refine)
  apply (simp_all)
  apply (simp add:tr_leq_trans)
done

subsection {* R2 Laws *}

(* L3 R2-idempotent *)

lemma R2s_idempotent: "`R2s(R2s(P))` = `R2s(P)`"
  apply (simp add:R2s_def)
  apply (subst SubstP_twice_2) back
  apply (simp_all add:typing defined closure unrest)
  apply (subst SubstP_twice_1) 
  apply (simp_all add:typing defined closure unrest)
  apply (simp add:usubst typing defined closure)
done

lemma R2s_destroys_R1: "R2s (R1 P) = R2s P" 
  by (simp add:R2s_def R1_def usubst closure typing defined)

lemma R2_idempotent: "`R2(R2(P))` = `R2(P)`" 
  by (simp add:R2_def R2s_destroys_R1 R2s_idempotent)

(* L4 R2-\<and>-closure *)

lemma R2s_AndP: 
  "`R2s(P \<and> Q)` = `R2s(P) \<and> R2s(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_AndP: "`R2(P \<and> Q)` = `R2(P) \<and> R2(Q)`"
  by (utp_pred_auto_tac)

lemma R2_AndP_closure: 
assumes "P is R2" "Q is R2"
shows "`P \<and> Q` is R2"
by (metis R2_AndP assms(1) assms(2) is_healthy_def)

(* L5 R2-\<or>-closure *)

lemma R2s_OrP: 
  "`R2s(A \<or> C)` = `R2s(A) \<or> R2s(C)`" 
  by (utp_pred_auto_tac)

lemma R2_OrP: "`R2(P \<or> Q)` = `R2(P) \<or> R2(Q)`"
  by (utp_pred_auto_tac)

lemma R2_OrP_closure: 
assumes "P is R2" "Q is R2"
shows "`P \<or> Q` is R2"
by (metis R2_OrP assms(1) assms(2) is_healthy_def)

(* L7 R2-cond-closure-2 *)

lemma R2s_CondR: 
  "`R2s(P \<lhd> b \<rhd> Q)` = `R2s(P) \<lhd> R2s(b) \<rhd> R2s(Q)`"
  by (utp_pred_auto_tac)

lemma R2_CondR: 
  "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2s(b) \<rhd> R2(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_CondR_alt: 
  "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2(b) \<rhd> R2(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_negate: 
  "`R2(\<not> b)` = `R1(\<not>R2(b))`"
by(utp_pred_auto_tac)

lemma R2_CondR_closure_2: 
assumes "P is R2" "Q is R2" "b is R2"
shows "`P \<lhd> b \<rhd> Q` is R2"
using assms 
proof -
  have "`R2(P \<lhd> b \<rhd> Q)`  = `(R2(b) \<and> R2(P)) \<or> (R1(\<not> R2(b)) \<and> R2(Q))`"
    by (utp_poly_auto_tac)
  also have "... = `(R2(b) \<and> R2(P)) \<or> (\<not> R2(b) \<and> R2(Q))`"
    by(utp_pred_auto_tac)
  also from assms have "... = `(b \<and> P) \<or> (\<not> b \<and> Q)`" 
    by(simp add:is_healthy_def)
  finally show ?thesis
    by (simp add:is_healthy_def CondR_def)
qed

(* L6 R2-cond-closure-1 *)

lemma tr_conserved_is_R2 : "`R2($tr\<acute> = $tr)` = `($tr\<acute> = $tr)`"
  apply(simp add:R2_def R2s_def R1_def usubst typing defined closure)
  apply (metis EqualP_sym tr_prefix_as_nil)
done

lemma R2_CondR_closure_1: 
assumes "P is R2" "Q is R2"
shows "`P \<lhd> ($tr\<acute> = $tr) \<rhd> Q` is R2"
by(subst R2_CondR_closure_2, simp_all add:assms, simp add:is_healthy_def tr_conserved_is_R2)

lemma RenamePV_aux [simp]:
  "pvaux (ss\<bullet>x) = pvaux x"
  by (metis PVAR_VAR_RENAME Rep_VAR_RENAME_aux pvaux_aux)

lemma SS1_UNREST_d3 [unrest]:
  "P \<in> WF_RELATION \<Longrightarrow> {x\<acute>\<acute>\<acute>} \<sharp> (SS1\<bullet>P)"
  apply (rule UNREST_RenameP[of "{x\<acute>\<acute>\<acute>}"])
  apply (simp_all add:unrest urename)
done

lemma SS2_UNREST_d3 [unrest]:
  "P \<in> WF_RELATION \<Longrightarrow> {x\<acute>\<acute>\<acute>} \<sharp> (SS2\<bullet>P)"
  apply (rule UNREST_RenameP[of "{x\<acute>\<acute>\<acute>}"])
  apply (simp_all add:unrest urename)
done

(* L9 R2-composition *)
(*R2 *)


abbreviation "tt1   \<equiv> MkPlainP ''tt1'' True TYPE('m EVENT ULIST) TYPE('m)"
abbreviation "tt2   \<equiv> MkPlainP ''tt2'' True TYPE('m EVENT ULIST) TYPE('m)"
abbreviation "tt   \<equiv> MkPlainP ''tt'' True TYPE('m EVENT ULIST) TYPE('m)"

lemma R2_form:
  assumes "P \<in> WF_RELATION" "pvaux ttx" 
  shows "R2(P) = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>\<acute>} . `P[\<langle>\<rangle>/tr][$ttx\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>)`)"
proof -
have "`$tr \<le> $tr\<acute>` = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>\<acute>} . `$tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>`)"
  by (metis (hide_lams, no_types) PVAR_VAR_pvdash assms(2) tr_prefix_as_concat)
hence "R2(P) = R2s(P) \<and>\<^sub>p (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>\<acute>} .  `$tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>`)"
  by(metis R2_def R1_def)
also have "... = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>\<acute>} . R2s(P) \<and>\<^sub>p `$tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>`)"
  apply(subst ExistsP_AndP_expand2)
  apply(rule unrest)
  apply(simp_all add:unrest assms closure)
  done  
also have "... = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>\<acute>} . `$tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>  \<and> R2s(P)`)"
  by(subst AndP_comm, simp)
also have  "... = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>\<acute>} . `R2s(P)[($tr ^ $ttx\<acute>\<acute>\<acute>)/tr\<acute>] \<and> $tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>`)"
  apply(simp add:erasure typing defined closure)
  apply(subst EqualP_SubstP)
  apply(simp_all add: typing defined closure assms AndP_comm)
  done
also have "... = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>\<acute>} . `P[\<langle>\<rangle>/tr][$ttx\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>)`)" 
  apply(simp add:R2s_def)
  apply(subst SubstP_twice_1)
  apply(simp_all add:typing defined closure assms)
  apply(simp add:usubst typing defined closure assms)
  apply(subst app_minus)
  apply(simp_all add:typing closure)
  done 
finally show ?thesis 
  by (metis assms(1))
qed  

lemma SS_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> SS\<bullet>P \<in> WF_RELATION"
  by (metis ConvR_def ConvR_rel_closure)

lemma append_assoc:
  fixes xs ys zs :: "(('a :: DEFINED) ULIST, 'm :: LIST_SORT) PVAR"
  shows "|($xs ^ $ys) ^ $zs| = |$xs ^ ($ys ^ $zs)|"
  by (utp_poly_tac)

(*
lemma "x \<in> PUNDASHED \<Longrightarrow> SS2 \<bullet> x\<acute>\<acute>\<acute> = x\<acute>\<acute>\<acute>"
*)

lemma EvalP_ExistsP_singleton_d3_pvaux_ty [evalp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "pvaux x"
  shows "\<lbrakk>\<exists>\<^sub>p {x\<down>\<acute>\<acute>\<acute>} . p\<rbrakk>b = (\<exists> v . v \<rhd>\<^sub>p x\<acute>\<acute>\<acute> \<and> \<lbrakk>p\<rbrakk>(b(x\<acute>\<acute>\<acute> :=\<^sub>* v)))"
  apply (subst EvalP_ExistsP_singleton_pvaux_ty[THEN sym])
  apply (simp_all add:assms)
done

lemma R2_SemiR_form: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "R2(P);R2(Q) =  `(\<exists> tt1\<acute>\<acute>\<acute>. \<exists> tt2\<acute>\<acute>\<acute>.  P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>))`"
  sorry

(*
proof -
    have "R2(P);R2(Q) = `( \<exists> tr \<acute>\<acute>\<acute> . 
      (\<exists> tt1\<acute>\<acute>\<acute> . (P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute>\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute>)));
      (\<exists> tt2\<acute>\<acute>\<acute> . (Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>)))
     )`"
        apply(subst SemiR_extract_variable_ty[of _ _ "tr"])
        apply(simp_all add:closure assms typing)
        apply(subst R2_form[of _ "tt1"])
        apply(simp_all add:closure assms)
        apply(subst R2_form[of _ "tt2"])
        apply(simp_all add:closure assms)
        apply(subst SubstP_ExistsP)
        apply(simp_all add:closure typing defined unrest)
        apply(subst SubstP_ExistsP)
        apply(simp_all add:closure typing defined unrest)
        apply(simp add:usubst typing defined)
        apply(simp add: SubstE_PSubstPE SubstE_PSubstPE_dash PSubstPE_Op2PE PSubstPE_PVarPE PSubstPE_PVarPE_different closure typing defined)
        apply(simp add:usubst typing defined closure)
        apply(subst SubstP_twice_3) back
        apply(simp_all add: typing defined closure unrest)
        apply(subst SubstP_twice_1)
        apply(simp_all add: typing defined closure unrest)
        apply (simp add:typing usubst defined closure)
        apply(subst SubstP_twice_3) back
        apply (simp_all add:usubst typing defined closure)
        apply (simp add:unrest typing defined closure)
   done
   also have "... = (\<exists>\<^sub>p {tr\<down>\<acute>\<acute>\<acute>} \<union> D\<^sub>2 \<union> {(prime on D\<^sub>1 \<bullet> tt1\<down>\<acute>\<acute>\<acute>)} \<union> {((prime \<circ> prime) on D\<^sub>0 \<bullet> tt2\<down>\<acute>\<acute>\<acute>)} . `(
      (prime on D\<^sub>1 \<bullet> P)[\<langle>\<rangle>/tr][$(prime on D\<^sub>1 \<bullet> tt1\<acute>\<acute>\<acute>)/tr\<acute>\<acute>] \<and> ($(prime on D\<^sub>1 \<bullet> tr\<acute>\<acute>\<acute>) = $(prime on D\<^sub>1 \<bullet> tr) ^ $(prime on D\<^sub>1 \<bullet> tt1\<acute>\<acute>\<acute>)) \<and>
      ((prime \<circ> prime) on D\<^sub>0 \<bullet> Q)[\<langle>\<rangle>/tr\<acute>\<acute>][$((prime \<circ> prime) on D\<^sub>0 \<bullet> tt2\<acute>\<acute>\<acute>)/tr\<acute>] \<and> ($((prime \<circ> prime) on D\<^sub>0 \<bullet> tr\<acute>) = $((prime \<circ> prime) on D\<^sub>0 \<bullet> tr\<acute>\<acute>\<acute>) ^ $((prime \<circ> prime) on D\<^sub>0 \<bullet> tt2\<acute>\<acute>\<acute>)))
`)"
     apply(subst SemiR_algebraic)
     apply(simp_all add:closure typing defined unrest urename assms)
     apply(subst ExistsP_AndP_expand1)
     defer 
     apply(subst ExistsP_AndP_expand2)
     defer 
     apply(subst ExistsP_union[THEN sym])
     apply(subst ExistsP_union[THEN sym])
     apply(subst ExistsP_union[THEN sym])
     apply(simp add:closure typing defined unrest urename)
     apply (metis (hide_lams, no_types) AndP_assoc)
     apply(rule unrest) back back back
     apply(rule unrest) 
     apply(rule UNREST_SubstP[of _ _ "{tt1\<down>\<acute>\<acute>\<acute>}" _ "{tt1\<down>\<acute>\<acute>\<acute>}"])
     apply(simp_all add:typing defined closure unrest urename assms)
   done
   also have "... = (\<exists>\<^sub>p {tr\<down>\<acute>\<acute>\<acute>} \<union> D\<^sub>2 \<union> { tt1\<down>\<acute>\<acute>\<acute>} \<union> { tt2\<down>\<acute>\<acute>\<acute>} . `(
      (prime on D\<^sub>1 \<bullet> P)[\<langle>\<rangle>/tr][$(prime on D\<^sub>1 \<bullet> tt1\<acute>\<acute>\<acute>)/tr\<acute>\<acute>] \<and> ($(prime on D\<^sub>1 \<bullet> tr\<acute>\<acute>\<acute>) = $(prime on D\<^sub>1 \<bullet> tr) ^ $(prime on D\<^sub>1 \<bullet> tt1\<acute>\<acute>\<acute>)) \<and>
      ((prime \<circ> prime) on D\<^sub>0 \<bullet> Q)[\<langle>\<rangle>/tr\<acute>\<acute>][$((prime \<circ> prime) on D\<^sub>0 \<bullet> tt2\<acute>\<acute>\<acute>)/tr\<acute>] \<and> ($((prime \<circ> prime) on D\<^sub>0 \<bullet> tr\<acute>) = $((prime \<circ> prime) on D\<^sub>0 \<bullet> tr\<acute>\<acute>\<acute>) ^ $((prime \<circ> prime) on D\<^sub>0 \<bullet> tt2\<acute>\<acute>\<acute>)))
`)"
  by(simp add:typing defined closure urename)
   also have "... = `(  \<exists> tt1\<acute>\<acute>\<acute> . \<exists> tt2\<acute>\<acute>\<acute> . \<exists> tr \<acute>\<acute>\<acute> .  
      (P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute>\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute>));
      (Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>))
     )`"
     apply(subst SemiR_algebraic)
     apply(rule unrest)
     apply(subst UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
     apply(simp_all add:closure typing defined unrest urename assms)
     apply(simp add:erasure typing defined closure)
     apply(subst ExistsP_union[THEN sym])
     apply(subst ExistsP_union[THEN sym])
     apply(subst ExistsP_union[THEN sym])
     apply(simp add:closure typing defined urename unrest assms)
     apply (smt AndP_assoc insert_commute)
  done
  also have "... = `(\<exists> tt1\<acute>\<acute>\<acute>. \<exists> tt2\<acute>\<acute>\<acute>. \<exists> tr\<acute>\<acute>\<acute>. ($tr\<acute>\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute>) \<and> P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>))`"
    apply(subst AndP_comm)
    apply(subst SemiR_AndP_left_precond)
    defer defer defer 
    apply(subst SemiR_AndP_right_postcond)
    defer defer defer 
    apply(simp_all add:assms unrest closure)
    sorry (* should be able to do things like SemiR_AndP_left_precond even when not WF_RELATION provided condition is free in dashed variables ? *)
  also have "... = `(\<exists> tt1\<acute>\<acute>\<acute>. \<exists> tt2\<acute>\<acute>\<acute>.  P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> (\<exists> tr\<acute>\<acute>\<acute>. ($tr\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>) \<and> ($tr\<acute>\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute>)))`"
    apply(subst AndP_comm)
    apply(subst AndP_assoc[THEN sym])
    apply(subst ExistsP_AndP_expand2[THEN sym])
    apply(simp_all add:unrest typing defined closure assms)
    sorry (*unrest problem *)
  also have "... = `(\<exists> tt1\<acute>\<acute>\<acute>. \<exists> tt2\<acute>\<acute>\<acute>.  P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>))`"
    proof -
      have  "`(\<exists> tr\<acute>\<acute>\<acute>. ($tr\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>) \<and> ($tr\<acute>\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute>))` = `($tr\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>)`" 
        apply(simp add:erasure typing defined closure)
        apply(subst ExistsP_one_point)
        apply(simp_all add:unrest typing defined closure)
        apply(subst SubstP_EqualP)
        apply(simp add:usubst typing defined closure append_assoc)
      done
      thus ?thesis 
        by metis
    qed
  finally show ?thesis
    ..
qed
*)

lemma R2_SemiR_distribute:
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "R2(P);R2(Q) is R2"
proof-
  have "R2(R2(P);R2(Q)) =  `(\<exists> tt1\<acute>\<acute>\<acute> . \<exists> tt2\<acute>\<acute>\<acute> . \<exists> tt\<acute>\<acute>\<acute> . P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tt\<acute>\<acute>\<acute> = $tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>) \<and> ($tr\<acute> = $tr ^ $tt\<acute>\<acute>\<acute>))`"
   apply(subst R2_form[of _ "tt"])
   apply(simp_all add:closure assms typing defined)
   apply(subst R2_SemiR_form)
   apply(simp_all add: assms)
   apply(subst SubstP_ExistsP)
   apply(simp_all add:unrest closure typing defined)
   apply(subst SubstP_ExistsP)
   apply(simp_all add:unrest closure typing defined)
   apply(subst SubstP_AndP)
   apply(subst SubstP_SemiR_left)
   apply(simp_all add:unrest closure typing defined)
   apply(subst SubstP_twice_2) back
   apply(simp_all add:unrest closure typing defined)
   apply(subst SubstP_EqualP)
   apply(subst SubstP_ExistsP)
   apply(simp_all add:unrest closure typing defined)
   apply(subst SubstP_ExistsP)
   apply(simp_all add:unrest closure typing defined)
   apply(subst SubstP_AndP)
   apply(subst SubstP_SemiR_right)
   apply(simp_all add:unrest closure typing defined)
   apply(subst SubstP_twice_1)
   apply(simp_all add:unrest closure typing defined)
   apply(subst SubstP_EqualP)
   apply(simp add:usubst typing defined closure)
   apply(subst ExistsP_AndP_expand1)
   apply(simp add:unrest closure typing defined)
   apply(subst ExistsP_AndP_expand1)
   apply(simp add:unrest closure typing defined)
   apply(subst AndP_assoc[THEN sym])
   apply(simp add: ExistsP_union[THEN sym])
   apply (metis insert_commute)
   done
   also have "... = `(\<exists> tt1\<acute>\<acute>\<acute> . \<exists> tt2\<acute>\<acute>\<acute> . P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> (\<exists> tt\<acute>\<acute>\<acute> . ($tt\<acute>\<acute>\<acute> = $tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>) \<and> ($tr\<acute> = $tr ^ $tt\<acute>\<acute>\<acute>)))`"
   apply(subst ExistsP_AndP_expand2[THEN sym])
   apply(simp_all add:unrest closure typing defined)
   sorry (*UNREST problem *)
   also have "... = `(\<exists> tt1\<acute>\<acute>\<acute> . \<exists> tt2\<acute>\<acute>\<acute> . P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>))`"
   apply(subst AndP_comm) back
   apply(simp add:PVarPE_erasure typing defined closure)
   apply(subst ExistsP_one_point[of _ "tt\<down>\<acute>\<acute>\<acute>"])
   apply(simp add:closure typing defined unrest erasure)
   apply(auto intro!:unrest closure typing simp add:typing closure)[1]
   apply(subst SubstP_EqualP)
   apply(simp add:usubst typing defined closure)
   done 
    also have "... = R2(P);R2(Q)" by(subst R2_SemiR_form,simp_all add:assms)
    finally show ?thesis by(simp add:is_healthy_def)
qed

lemma R2_SemiR_closure: 
assumes "P is R2" "Q is R2" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "P;Q is R2"
by (metis Healthy_simp R2_SemiR_distribute assms)

lemma R2_sequential_composition: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`R2(P);R2(Q)` = `R2(P ; R2(Q))`"
proof -
  have 1: "`R2(P);R2(Q)` = `R2(R2(P);R2(Q))`"  
    by (metis R2_SemiR_distribute assms is_healthy_def)
  have 2: "R2(P);R2(Q)  = (\<exists>\<^sub>p {tt\<down>\<acute>\<acute>\<acute>,tt1\<down>\<acute>\<acute>\<acute>,tt2\<down>\<acute>\<acute>\<acute>} . `(P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tt\<acute>\<acute>\<acute> = $tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>) \<and> ($tr\<acute> = $tr ^ $tt\<acute>\<acute>\<acute>))`)"
    apply(subst 1)
    apply(subst R2_form[of _ "tt"])
    apply(metis assms closure)
    apply (metis pvaux_MkPVAR)
    apply(subst R2_SemiR_form)
    apply(simp_all add:assms)
    apply(subst SubstP_ExistsP)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SubstP_ExistsP)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SubstP_AndP)
    apply(subst SubstP_SemiR_left)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SubstP_twice_2) back
    apply(simp_all add:closure typing defined unrest)
    apply(subst SubstP_EqualP)
    apply(subst SubstP_ExistsP)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SubstP_ExistsP)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SubstP_AndP)
    apply(subst SubstP_SemiR_right)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SubstP_twice_1)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SubstP_EqualP)
    apply(simp add:usubst typing defined closure)
    apply(subst ExistsP_AndP_expand1)
    apply(simp_all add:closure typing defined unrest)
    apply(subst ExistsP_AndP_expand1)
    apply(simp_all add:closure typing defined unrest)
    apply(subst ExistsP_union[THEN sym])
    apply(subst ExistsP_union[THEN sym])
    apply (smt AndP_assoc Un_insert_left sup_bot_left)
    done
  have "R2(P ; R2(Q)) =  (\<exists>\<^sub>p {tt\<down>\<acute>\<acute>\<acute>} . (\<exists>\<^sub>p {tr\<down>\<acute>\<acute>\<acute>} . 
    `P[\<langle>\<rangle>/tr][$tr\<acute>\<acute>\<acute>/tr\<acute>] ; (\<exists> tt2\<acute>\<acute>\<acute> . Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tt\<acute>\<acute>\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>)) \<and>
     ($tr\<acute> = $tr ^ $tt\<acute>\<acute>\<acute>)`))"
    apply(subst R2_form[of _ "tt"])
    apply(metis assms closure)
    apply (metis pvaux_MkPVAR)
    apply(subst SemiR_extract_variable_ty[of _ _ "tr "])
    apply(simp_all add:assms closure typing)
    apply(subst SubstP_ExistsP)
    apply(simp_all add:typing closure unrest defined)
    apply(subst SubstP_SemiR_left)
    apply(simp_all add:typing closure unrest defined)
    apply(subst SubstP_twice_3)
    apply(simp_all add:typing closure unrest defined)
    apply(subst SubstP_ExistsP)
    apply(simp_all add:typing closure unrest defined)
    apply(subst SubstP_SemiR_right)
    apply(simp_all add:typing closure unrest defined)
    apply(simp add:erasure typing defined closure)
(*    apply(simp add:usubst typing defined closure assms) *)
    apply(subst R2_form[of _ "tt2"])
    apply(metis assms(2))
    apply (metis pvaux_MkPVAR)
    apply(subst SubstP_ExistsP)
    apply(simp_all add:typing closure unrest defined)
    apply(subst SubstP_AndP)
    apply(subst SubstP_twice_2) back back
    apply(simp_all add:typing closure unrest defined)
    apply(subst SubstP_ExistsP)
    apply(simp_all add:typing closure unrest defined)
    apply(subst SubstP_AndP)
    apply(subst SubstP_twice_1)
    apply(simp_all add:typing closure unrest defined)
    apply(subst SubstP_EqualP)
    apply(subst SubstP_EqualP)
    sorry
(*
    apply(simp add:usubst typing defined closure)
    apply(subst ExistsP_AndP_expand1)
    apply(simp_all add:typing defined closure unrest)
    done
*)
  also have "... = (\<exists>\<^sub>p D\<^sub>2 \<union> {tt\<down>\<acute>\<acute>\<acute>,tr\<down>\<acute>\<acute>\<acute>,tt2\<down>\<acute>\<acute>\<acute>} .
     `(prime on D\<^sub>1 \<bullet> P)[\<langle>\<rangle>/tr][$(prime on D\<^sub>1 \<bullet> tr\<acute>\<acute>\<acute>)/tr\<acute>\<acute>] \<and>
      ((prime \<circ> prime) on D\<^sub>0 \<bullet> Q)[\<langle>\<rangle>/tr\<acute>\<acute>][$((prime \<circ> prime) on D\<^sub>0 \<bullet> tt2\<acute>\<acute>\<acute>)/tr\<acute>] \<and> ($((prime \<circ> prime) on D\<^sub>0 \<bullet> tt\<acute>\<acute>\<acute>) = $((prime \<circ> prime) on D\<^sub>0 \<bullet> tr\<acute>\<acute>\<acute>) ^ $((prime \<circ> prime) on D\<^sub>0 \<bullet> tt2\<acute>\<acute>\<acute>)) \<and>
     ($tr\<acute> = $tr ^ $tt\<acute>\<acute>\<acute>)`)"
     apply(subst SemiR_algebraic)
     apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
     apply(simp_all add:closure typing defined unrest)
     apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
     apply(simp_all add:closure typing defined unrest assms)
     apply(subst ExistsP_AndP_expand1)
     apply(simp add:typing unrest defined closure assms)
     apply (simp add:urename closure typing defined assms)
(*    apply(rule unrest)
     apply(rule unrest)
     apply(simp add:typing defined closure)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply(rule unrest)
     apply(simp add:typing defined closure)
     apply(rule unrest)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply (metis dash_DASHED_TWICE_elim undash_dash undash_eq_dash_contra1)
     apply(subst ExistsP_AndP_expand1)
     apply(rule unrest) back back
     apply(simp add:erasure typing defined closure)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply(rule unrest)
     apply(simp add:typing defined closure)
     apply(rule unrest)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply(subst ExistsP_union[THEN sym])
     apply(subst ExistsP_union[THEN sym])
     apply(subst ExistsP_union[THEN sym])
     apply (smt AndP_assoc Un_insert_left Un_insert_right sup_bot_left sup_bot_right)*)
     sorry (* more little bits *)
also have "... = (\<exists>\<^sub>p {tt\<down>\<acute>\<acute>\<acute>,tr\<down>\<acute>\<acute>\<acute>,tt2\<down>\<acute>\<acute>\<acute>} .  
    `P[\<langle>\<rangle>/tr][$tr\<acute>\<acute>\<acute>/tr\<acute>] ; (Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tt\<acute>\<acute>\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>)) \<and>
     ($tr\<acute> = $tr ^ $tt\<acute>\<acute>\<acute>)`)"
     apply(subst SemiR_algebraic)
     apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
     apply(simp_all add:typing defined closure unrest)
     apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
     apply(simp_all add:typing defined closure unrest assms)
     apply(simp add:erasure typing defined closure)
(*
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply (metis DASHED_dash_not_DASHED MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_dash_DASHED dash_DASHED_TWICE_elim) 
     apply(rule unrest)
     apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
     apply(simp_all add:typing defined closure unrest assms)
     apply(simp add:erasure typing defined closure)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply (metis DASHED_dash_not_DASHED MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_dash_DASHED dash_DASHED_TWICE_elim) 
     apply(rule unrest)
     apply(simp add:erasure typing defined closure)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply (metis DASHED_dash_not_DASHED MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_dash_DASHED dash_DASHED_TWICE_elim) 
     apply(rule unrest)
     apply(simp add:typing defined closure)
     apply(rule unrest)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply (metis DASHED_dash_not_DASHED MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_dash_DASHED dash_DASHED_TWICE_elim) 
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply (metis DASHED_dash_not_DASHED MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_dash_DASHED dash_DASHED_TWICE_elim) 
     apply (subst ExistsP_AndP_expand1)
     apply(rule unrest)
     apply(simp add:erasure typing defined closure)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply(rule unrest)
     apply(simp add:typing defined closure)
     apply(rule unrest)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply(rule unrest)
     apply(utp_pred_auto_tac)
     apply (metis DASHED_dash_not_DASHED MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_dash_DASHED dash_DASHED_TWICE_elim) 
     apply(subst ExistsP_union[THEN sym])
     apply(simp add:typing defined closure urename)
     apply (smt AndP_assoc)
     done *)
     sorry
  also have "... = (\<exists>\<^sub>p {tt\<down>\<acute>\<acute>\<acute>,tr\<down>\<acute>\<acute>\<acute>,tt2\<down>\<acute>\<acute>\<acute>} .  
    `P[\<langle>\<rangle>/tr][$tr\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> 
      ($tt\<acute>\<acute>\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>) \<and> ($tr\<acute> = $tr ^ $tt\<acute>\<acute>\<acute>)`)"
      apply(subst SemiR_AndP_right_postcond)
      defer defer defer 
      apply(utp_pred_auto_tac)
     sorry (*SemiR_AndP_right_postcond on non WF_RELATION *)
   finally have 3: "R2(P;R2(Q)) = (\<exists>\<^sub>p {tt\<down>\<acute>\<acute>\<acute>,tr\<down>\<acute>\<acute>\<acute>,tt2\<down>\<acute>\<acute>\<acute>} .  
    `P[\<langle>\<rangle>/tr][$tr\<acute>\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tt\<acute>\<acute>\<acute> = $tr\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>) \<and> ($tr\<acute> = $tr ^ $tt\<acute>\<acute>\<acute>)`)"
      ..
   show ?thesis 
      apply(subst 2) 
      apply(subst 3)
      sorry (*renaming a quantified variable *)
qed

lemma R2_composition: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "R2(P ; R2(Q)) = R2(P) ; R2(Q)"
by (metis R2_sequential_composition assms(1) assms(2))
   
(* L10 R2-wait-okay' *)

lemma R2_wait_true: "(R2(P))\<^sub>t = R2(P\<^sub>t)"
  apply(simp add:R2_def R1_wait_true R2s_def)
  apply(subst SubstP_twice_3) back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  apply(subst SubstP_twice_3) back back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  done

lemma R2_wait_false: "(R2(P))\<^sub>f = R2(P\<^sub>f)"
  apply(simp add:R2_def R1_wait_false R2s_def)
  apply(subst SubstP_twice_3) back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  apply(subst SubstP_twice_3) back back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  done

(* L14 commutativity R2-R1 *)

lemma R1_R2_commute: 
  "R1 (R2 P) = R2 (R1 P)" 
by (simp add:R2_def R1_idempotent R2s_destroys_R1)

(* Additional lemmas *)

lemma R2_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R2(P) \<sqsubseteq> R2(Q)" 
  by utp_pred_tac

lemma SkipRA_is_R2 : "`R2(II)` = `II`"
proof -
  have "`R2(II\<^bsub>REL_VAR\<^esub>)` = `(($tr\<acute> - $tr) = \<langle>\<rangle> \<and> II\<^bsub>REL_VAR - TR\<^esub>) \<and> ($tr \<le> $tr\<acute>)`"
    apply (simp add:R1_def R2_def R2s_def)
    apply (subst SkipRA_unfold[of "tr\<down>"])
    apply (auto simp add:closure)
    apply (simp add:usubst closure typing defined)
  done

  also have "... = `(($tr\<acute> - $tr) = \<langle>\<rangle> \<and> ($tr \<le> $tr\<acute>)) \<and> II\<^bsub>REL_VAR - TR\<^esub>`"
    by (metis (hide_lams, no_types) AndP_assoc AndP_comm)

  also have "... = `$tr\<acute> = $tr \<and> II\<^bsub>REL_VAR - TR\<^esub>`"
    by (metis EqualP_sym tr_prefix_as_nil)

  also have "... = `II\<^bsub>REL_VAR\<^esub>`"
    apply (subst SkipRA_unfold[of "tr\<down>"]) back
    apply (auto simp add:closure erasure typing)
  done

  finally show ?thesis 
    by(simp add:SkipR_as_SkipRA)
qed

subsection {* R3 Laws *}

(* L1 R3-wait-true *)

lemma R3_wait_true: 
  "`(R3(P))\<^sub>t` = `II\<^sub>t` "
by(simp add:R3_def usubst typing defined closure CondR_def)

(* L2 R3-wait-false *)

lemma R3_wait_false: 
  "`(R3(P))\<^sub>f` = `P\<^sub>f` "
by(simp add:R3_def usubst typing defined closure CondR_def)

(* L4 closure-\<and>-R3 *)

lemma R3_AndP: 
  "`R3(P \<and> Q)` = `R3(P) \<and> R3(Q)`"
by(utp_pred_auto_tac)

lemma R3_AndP_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<and> Q` is R3"
by(metis is_healthy_def R3_AndP assms)

(* L5 closure-\<or>-R3 *)

lemma R3_OrP: 
  "`R3(P \<or> Q)` = `R3(P) \<or> R3(Q)`"
by(utp_pred_auto_tac)

lemma R3_OrP_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<or> Q` is R3"
by(metis is_healthy_def R3_OrP assms)
  
(* L6 closure-conditional-R3 *)

lemma R3_CondR: 
  "`R3(P  \<lhd> b \<rhd> Q)` = `R3(P) \<lhd> b \<rhd> R3(Q)`"
by(utp_pred_auto_tac)

lemma R3_CondR_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<lhd> b \<rhd> Q` is R3"
by(metis is_healthy_def R3_CondR assms)

(* L7 closure-sequence-R3 *)

lemma R3_form : "`R3(P)` = `($wait  \<and> II) \<or> (\<not>$wait \<and> P)`"
  by(simp add:R3_def CondR_def)

lemma R3_wait: "`R3(P) \<and> $wait` = `II \<and> $wait`"
  apply (simp add:R3_def)
  apply (subst AndP_comm)
  apply (subst CondR_true_cond)
  apply (subst AndP_comm)
  apply (rule refl)
done

lemma wait_and_II: "`$wait \<and> II` =`$wait \<and> II \<and> $wait\<acute>`"
  apply(simp add:SkipR_as_SkipRA)
  apply(subst SkipRA_unfold[of "wait \<down>"])
  apply(simp_all add:closure)
  apply(subst SkipRA_unfold[of "wait \<down>"]) back
  apply(simp_all add:closure)
  apply(utp_pred_auto_tac)
done

theorem R3_SemiR_form:
  assumes
    "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "R3(P);R3(Q) = R3(P;R3(Q))"
    apply(simp add:R3_form SemiR_OrP_distl SemiR_OrP_distr)
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined WF_RELATION_UNREST unrest urename)
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined WF_RELATION_UNREST unrest urename assms(1))
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined WF_RELATION_UNREST unrest urename assms(2))
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined WF_RELATION_UNREST unrest urename assms(1) assms(2))
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined WF_RELATION_UNREST unrest urename assms(1) assms(2))
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined WF_RELATION_UNREST unrest urename assms(1) assms(2))
    apply(subst wait_and_II) back
    apply(subst wait_and_II) back
    apply(simp add:AndP_OrP_distl AndP_assoc[THEN sym])
    apply(subst SemiR_AndP_left_precond[where c="`\<not>$wait`"])
    apply(simp_all add:closure typing defined WF_RELATION_UNREST unrest urename assms(1) assms(2))
    apply(simp add:AndP_contra)
    apply(utp_pred_auto_tac)
done

lemma R3_SemiR_closure[closure]: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R3" "Q is R3"
  shows "P ; Q is R3"
by (metis Healthy_intro Healthy_simp R3_SemiR_form assms(1) assms(2) assms(3) assms(4))

(* L8 R3-idempotent *)

lemma R3_idempotent: "`R3(R3(P))` = `R3(P)`" 
  by (utp_pred_auto_tac)

(* L10 commutativity-R3-R1 *)

lemma R1_R3_commute: "R1 (R3 P) = R3 (R1 P)" 
proof - 
  have "R1 (R3 P) = `(II \<lhd> $wait \<rhd> P) \<and> ($tr \<le> $tr\<acute>)`" 
    by utp_rel_tac
  also have "... = `(II \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait \<rhd> (P \<and> ($tr \<le> $tr\<acute>))`" 
    by utp_pred_auto_tac
  also have "... = `II \<lhd> $wait \<rhd> (P \<and> ($tr \<le> $tr\<acute>))`" 
    by (metis R1_SkipR R1_def)
  ultimately show ?thesis by utp_pred_auto_tac
qed

(* L11 commutativite-R3-R2 *)

theorem R2_R3_commute: 
  "R2 (R3 P) = R3 (R2 P)" 
proof - 
  have "R2 (R3 P) = `R2(II) \<lhd> R2s($wait) \<rhd> R2(P)`" 
    by (simp add:R3_def R2_CondR)
  also have "... = `II \<lhd> $wait \<rhd> R2(P)`"
    apply(simp add:R2s_def usubst typing defined closure)
    by (metis SkipRA_is_R2)
  finally show ?thesis 
    by (simp add: R3_def R2_def)
qed

(* Additional Lemmas *)

lemma R3_SkipREA: "`R3(II)` = `II`"
  by (simp add:R3_def CondR_idem)

declare CondR_def [evalp]
declare less_eq_WF_PREDICATE_def [evalp]

lemma R3_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R3(P) \<sqsubseteq> R3(Q)"
  by utp_poly_tac 
  
subsection {* RH Laws *}

lemma RH_is_R1:
  "P is RH \<Longrightarrow> P is R1"
  by (metis Healthy_intro Healthy_simp R1_idempotent RH_def comp_apply)

lemma RH_is_R2:
  "P is RH \<Longrightarrow> P is R2"
  by (metis Healthy_intro Healthy_simp R1_idempotent R2_R3_commute R2_def R3_idempotent RH_def comp_apply)

lemma RH_is_R3:
  "P is RH \<Longrightarrow> P is R3"
  by (metis Healthy_intro Healthy_simp R1_R3_commute R1_idempotent R2_R3_commute R2_def R3_idempotent RH_def o_eq_dest_lhs)

lemma R_intro: "\<lbrakk> P is R1; P is R2; P is R3 \<rbrakk> \<Longrightarrow> P is RH"
  by (metis RH_def comp_apply is_healthy_def)

(* L1 reactive-left-zero *)

lemma R1_true_left_zero: 
  assumes "P is R1" "P is R3" "P \<in> WF_RELATION"
  shows "`($tr \<le> $tr\<acute>) ; P` = `($tr \<le> $tr\<acute>) \<and> ($wait\<acute> \<or> ($tr \<le> $tr\<acute>);P\<^sub>f)`"
proof -
have 1: "`($wait\<acute> \<and> II)` = `($wait \<and> $wait\<acute> \<and> II)`"
  apply(simp add:SkipR_as_SkipRA)
  apply(subst SkipRA_unfold[of "wait \<down>"])
  apply(simp_all add:closure)
  apply(subst SkipRA_unfold[of "wait \<down>"])back
  apply(simp_all add:closure)
  apply(utp_pred_auto_tac)
  done
have "P = `($wait \<and> II) \<or> (\<not>$wait \<and> P)`"
  by (metis Healthy_simp R3_form assms(2))
hence "`($tr \<le> $tr\<acute>) ; P` = `($tr \<le> $tr\<acute>) ; ($wait \<and> II) \<or> ($tr \<le> $tr\<acute>) ; (\<not>$wait \<and> P)`"
  by (metis (hide_lams, no_types) SemiR_OrP_distl)
also have "... = `($tr \<le> $tr\<acute>) ; ($wait \<and> $wait\<acute> \<and> II ) \<or> ($tr \<le> $tr\<acute>) ; (\<not>$wait \<and> P)`"
  by (metis AndP_comm wait_and_II)
also have "... = `($tr \<le> $tr\<acute>) ; (II \<and> $wait\<acute>) \<or> ($tr \<le> $tr\<acute>) ; (\<not>$wait \<and> P)`"
  by (metis "1" AndP_comm)
also have "... = `(($tr \<le> $tr\<acute>) \<and> $wait\<acute>) \<or> ($tr \<le> $tr\<acute>) ; (\<not>$wait \<and> P\<^sub>f)`"
  apply(subst SemiR_AndP_right_postcond)
  apply(simp_all add:closure)
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply(subst NotP_PVarPE_PSubstPE)
  apply(simp_all add:closure typing)
  done
also have "... =  `(($tr \<le> $tr\<acute>) \<and> $wait\<acute>) \<or> ($tr \<le> $tr\<acute>) ; P\<^sub>f`"
  apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait \<down>}"])
  apply(simp_all add:closure typing defined erasure unrest)
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply(subst SubstP_rel_closure)
  apply(simp_all add:assms closure typing defined WF_RELATION_UNREST unrest)
  done
also have "... = `(($tr \<le> $tr\<acute>) \<and> $wait\<acute>) \<or> R1(($tr \<le> $tr\<acute>) ; P\<^sub>f)`"
  proof-
    have "`P\<^sub>f` is R1"
      apply(simp add:is_healthy_def R1_wait_false[THEN sym])
      by (metis Healthy_simp assms(1))
    hence "`($tr \<le> $tr\<acute>) ; P\<^sub>f` is R1"
      apply(subst R1_SemiR_closure)
      apply(simp_all add:closure is_healthy_def R1_def assms typing defined WF_RELATION_UNREST unrest)
      done
    thus ?thesis 
      by (metis is_healthy_def)
    qed
finally show ?thesis 
  by(utp_pred_auto_tac) 
qed

(* L2 restricted-identity *)

lemma Skip_identity:
  assumes "P is RH" "P \<in> WF_RELATION"
  shows " `II ; P` = P"
by (metis SemiR_SkipR_left)

(* L3 R-wait-false *)

lemma RH_wait_false: 
  "`(RH(P))\<^sub>f` = `R1(R2(P\<^sub>f))`"
by(simp add:RH_def R1_wait_false R2_wait_false R3_wait_false)

(* L4 R-wait-true *)

lemma RH_wait_true: 
  "`(RH(P))\<^sub>t` = `II\<^sub>t`"
by(simp add:RH_def R2_R3_commute R1_R3_commute R3_wait_true)

(* L6 closure-\<and>-R *)

lemma RH_AndP_closure:
  assumes "P is RH" "Q is RH"
  shows "`P \<and> Q` is RH"
proof -
  have "`R3(P \<and> Q)` = `P \<and> Q`" 
    by (metis Healthy_simp R3_AndP RH_is_R3 assms(1) assms(2))
  hence "`R2(R3(P \<and> Q))` = `P \<and> Q`" 
    by (metis R2_AndP RH_is_R2 assms(1) assms(2) is_healthy_def)
  hence "`R1(R2(R3(P \<and> Q)))` = `P \<and> Q`" 
    by (metis R1_idempotent R2_def)
  thus ?thesis 
    by(simp add:is_healthy_def RH_def)
qed

(* L7 closure-\<or>-R *)

lemma RH_OrP_closure:
  assumes "P is RH" "Q is RH"
  shows "`P \<or> Q` is RH"
proof -
  have "`R3(P \<or> Q)` = `P \<or> Q`" 
    by (metis Healthy_simp R3_OrP RH_is_R3 assms(1) assms(2))
  hence "`R2(R3(P \<or> Q))` = `P \<or> Q`" 
    by (metis R2_OrP RH_is_R2 assms(1) assms(2) is_healthy_def)
  hence "`R1(R2(R3(P \<or> Q)))` = `P \<or> Q`" 
    by (metis R1_idempotent R2_def)
  thus ?thesis 
    by(simp add:is_healthy_def RH_def)
qed

(* L8 closure-cond-R *)

lemma RH_CondR_closure:
  assumes "P is RH" "Q is RH" "b is R2s"
  shows "`P \<lhd> b \<rhd> Q` is RH"
proof -
  have "`R3(P \<lhd> b \<rhd> Q)` = `P \<lhd> b \<rhd> Q`" by (metis Healthy_simp R3_CondR RH_is_R3 assms(1) assms(2))
  hence "`R2(R3(P \<lhd> b \<rhd> Q))` = `P \<lhd> b \<rhd> Q`" by (metis R2_CondR RH_is_R2 assms(1) assms(2) assms(3) is_healthy_def)
  hence "`R1(R2(R3(P \<lhd> b \<rhd> Q)))` = `P \<lhd> b \<rhd> Q`" by (metis R1_idempotent R2_def)
  thus ?thesis by(simp add:is_healthy_def RH_def)
qed

(* L9 closure-sequence-R *)

lemma RH_SemiR_closure:
  assumes "P \<in> WF_RELATION" "Q\<in> WF_RELATION" "P is RH" "Q is RH"
  shows "`P ; Q` is RH"
by (metis R1_SemiR_closure R2_SemiR_closure R3_SemiR_closure RH_is_R1 RH_is_R2 RH_is_R3 R_intro assms(1) assms(2) assms(3) assms(4))

subsection {* The theory of Reactive Processes *}

lift_definition REACTIVE :: "'VALUE WF_THEORY" 
is "({vs. vs \<subseteq> REL_VAR \<and> REA \<subseteq> vs}, {R1,R2,R3})"
  by (simp add:WF_THEORY_def IDEMPOTENT_OVER_def R1_idempotent R2_idempotent R3_idempotent)
      
end