section {* Reactive design tactics *}

theory utp_rdes_tactics
  imports utp_rdes_triples
begin

text \<open> Theorems for normalisation \<close>

lemmas rdes_rel_norms = 
  prod.case_eq_if
  conj_assoc
  disj_assoc
  utp_pred_laws.distrib(3,4)
  conj_UINF_dist
  conj_UINF_ind_dist
  seqr_or_distl
  seqr_or_distr
  seq_UINF_distl
  seq_UINF_distl'
  seq_UINF_distr
  seq_UINF_distr'

text {* The following tactic can be used to simply and evaluate reactive predicates. *}

method rpred_simp = (uexpr_simp simps: rpred usubst closure unrest)

text {* Tactic to expand out healthy reactive design predicates into the syntactic triple form. *}
  
method rdes_expand uses cls = (insert cls, (erule RD_elim)+)    

text {* Tactic to simplify the definition of a reactive design *}
  
method rdes_simp uses cls cong simps =
  ((rdes_expand cls: cls)?, (simp add: closure)?, (simp add: rdes_def rdes_rel_norms rdes rpred cls closure alpha frame usubst unrest wp simps cong: cong))

text {* Tactic to split a refinement conjecture into three POs *}

method rdes_refine_split uses cls cong simps =
  (rdes_simp cls: cls cong: cong simps: simps; rule_tac srdes_tri_refine_intro')

text {* Tactic to split an equality conjecture into three POs *}

method rdes_eq_split uses cls cong simps =
  (rdes_simp cls: cls cong: cong simps: simps; (rule_tac srdes_tri_eq_intro))

text {* Tactic to prove a refinement *}
  
method rdes_refine uses cls cong simps =
  (rdes_refine_split cls: cls cong: cong simps: simps; (insert cls; rel_auto))

text {* Tactics to prove an equality *}

method rdes_eq uses cls cong simps =
  (rdes_eq_split cls: cls cong: cong simps: simps; rel_auto)

text {* Via antisymmetry *}

method rdes_eq_anti uses cls cong simps =
  (rdes_simp cls: cls cong: cong simps: simps; (rule_tac antisym; (rule_tac srdes_tri_refine_intro; rel_auto)))

text {* Tactic to calculate pre/peri/postconditions from reactive designs *}

method rdes_calc = (simp add: rdes rpred closure alpha usubst unrest wp prod.case_eq_if)

text {* The following tactic attempts to prove a reactive design refinement by calculation of
  the pre-, peri-, and postconditions and then showing three implications between them using
  rel-blast. *}

method rdspl_refine =
  (rule_tac SRD_refine_intro; (simp add: closure rdes unrest usubst ; rel_blast?))

text {* The following tactic combines antisymmetry with the previous tactic to prove an equality. *}

method rdspl_eq =
  (rule_tac antisym, rdes_refine, rdes_refine)  

end