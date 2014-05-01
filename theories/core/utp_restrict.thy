theory utp_restrict
imports 
  utp_pred 
  utp_unrest 
  utp_expr 
  utp_rel
begin

(* Restriction forcibly removes a set of variables from a predicate by substituting
   the default value for them. This method is better than through quantification since
   it distributes through the predicate operators. *)

lift_definition RestrictP :: "'a WF_PREDICATE \<Rightarrow> 'a VAR set \<Rightarrow> 'a WF_PREDICATE" 
is "\<lambda> p xs. {b. b \<oplus>\<^sub>b \<B> on xs \<in> p}" .

notation RestrictP (infixr "\<ominus>\<^sub>p" 200)

lift_definition RestrictE :: "'a WF_EXPRESSION \<Rightarrow> 'a VAR set \<Rightarrow> 'a WF_EXPRESSION"
is "\<lambda> f xs. (\<lambda> b. \<langle>f\<rangle>\<^sub>e (b \<oplus>\<^sub>b \<B> on xs))"
  apply (simp add:WF_EXPRESSION_def)
  apply (metis Rep_WF_EXPRESSION_typed)
done

notation RestrictE (infixr "\<ominus>\<^sub>e" 200)

lemma RestrictP_TrueP:
  "true \<ominus>\<^sub>p vs = true"
  by (auto simp add:RestrictP.rep_eq TrueP.rep_eq)

lemma RestrictP_FalseP:
  "false \<ominus>\<^sub>p vs = false"
  by (auto simp add:RestrictP.rep_eq FalseP.rep_eq)

lemma RestrictP_NotP:
  "(\<not>\<^sub>p p) \<ominus>\<^sub>p vs = (\<not>\<^sub>p (p \<ominus>\<^sub>p vs))"
  by (auto simp add:RestrictP.rep_eq NotP.rep_eq)

lemma RestrictP_OrP:
  "(p \<or>\<^sub>p q) \<ominus>\<^sub>p vs = (p \<ominus>\<^sub>p vs) \<or>\<^sub>p (q \<ominus>\<^sub>p vs)"
  by (auto simp add:RestrictP.rep_eq OrP.rep_eq)

lemma RestrictP_AndP:
  "(p \<and>\<^sub>p q) \<ominus>\<^sub>p vs = (p \<ominus>\<^sub>p vs) \<and>\<^sub>p (q \<ominus>\<^sub>p vs)"
  by (auto simp add:RestrictP.rep_eq AndP.rep_eq)

lemma RestrictP_ExprP:
  "(ExprP e) \<ominus>\<^sub>p vs = (ExprP (e \<ominus>\<^sub>e vs))"
  by (auto simp add:ExprP_def LiftP.rep_eq RestrictP.rep_eq RestrictE.rep_eq)

lemma RestrictP_VarE:
  "x \<notin> vs \<Longrightarrow> ($\<^sub>ex) \<ominus>\<^sub>e vs = $\<^sub>ex"
  by (auto simp add:RestrictE.rep_eq VarE.rep_eq)

lemma RestrictP_LitE:
  "(LitE v) \<ominus>\<^sub>e xs = LitE v"
  by (auto simp add:RestrictE.rep_eq LitE_rep_eq)

lemma RestrictP_SkipR:
  "\<lbrakk> xs \<subseteq> REL_VAR; HOMOGENEOUS xs \<rbrakk> \<Longrightarrow> II \<ominus>\<^sub>p (- xs) = II\<^bsub>xs\<^esub>"
  apply (rule)
  apply (auto simp add:SkipR.rep_eq SkipRA.rep_eq ExistsP.rep_eq RestrictP.rep_eq)
  apply (rule_tac x="x \<oplus>\<^sub>b \<B> on REL_VAR - xs" in exI)
  apply (auto)
  apply (rule_tac x="x" in exI, simp)
  apply (drule_tac x="v" in bspec, auto)
  apply (metis (hide_lams, no_types) Compl_iff Diff_iff UNDASHED_dash_DASHED Un_iff override_on_apply_in override_on_apply_notin)
  apply (metis (hide_lams, mono_tags) Compl_iff default_binding_dash hom_alphabet_dash hom_alphabet_undash override_on_apply_in override_on_apply_notin override_on_minus)
done

lemma RestrictP_SemiR:
  "(p ;\<^sub>R q) \<ominus>\<^sub>p xs = (p \<ominus>\<^sub>p (in(xs) \<union> nrel(xs))) ;\<^sub>R (q \<ominus>\<^sub>p (out(xs) \<union> nrel(xs)))"
  apply (rule) 
  apply (auto simp add:SemiR.rep_eq RestrictP.rep_eq)
oops

lemma UNREST_RestrictP [unrest]:
  "vs \<sharp> p \<ominus>\<^sub>p vs"
  by (simp add: UNREST_def RestrictP.rep_eq)

lemma UNREST_RestrictE [unrest]:
  "vs \<sharp> p \<ominus>\<^sub>e vs"
  apply (subst UNREST_EXPR_def)
  apply (simp add: RestrictE.rep_eq)
done

end