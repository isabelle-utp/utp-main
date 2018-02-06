section {* Design Proof Tactics *}

theory utp_des_tactics
  imports utp_des_theory
begin

text {* The tactics split apart a healthy normal design predicate into its pre-postcondition form, 
  using elimination rules, and then attempt to prove refinement conjectures. *}

named_theorems ND_elim
  
lemma ndes_elim: "\<lbrakk> P is \<^bold>N; Q(\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: ndesign_form)
    
lemma ndes_split [ND_elim]: "\<lbrakk> P is \<^bold>N; \<And> pre post. Q(pre \<turnstile>\<^sub>n post) \<rbrakk> \<Longrightarrow> Q(P)"
  by (metis H1_H2_eq_rdesign H1_H3_impl_H2 H3_unrest_out_alpha Healthy_def drop_pre_inv ndesign_def)

text {* Use given closure laws (cls) to expand normal design predicates *}

method ndes_expand uses cls = (insert cls, (erule ND_elim)+)

text {* Expand and simplify normal designs *}

method ndes_simp uses cls =
  ((ndes_expand cls: cls)?, (simp add: ndes_simp closure alpha usubst unrest wp prod.case_eq_if))

text {* Attempt to discharge a refinement between two normal designs *}

method ndes_refine uses cls =
  (ndes_simp cls: cls; rule_tac ndesign_refine_intro; (insert cls; rel_simp; auto?))

text {* Attempt to discharge an equality between two normal designs *}

method ndes_eq uses cls =
  (ndes_simp cls: cls; rule_tac antisym; rule_tac ndesign_refine_intro; (insert cls; rel_simp; auto?))

end