section {* Imperative Programs *}
  
theory utp_prog
  imports "../theories/utp_designs"
begin
  
subsection {* Program Type *}
  
typedef '\<alpha> prog = "{P :: '\<alpha> hrel_des. P is \<^bold>N}"
  by (rule_tac x="true" in exI, simp add: closure)
    
named_theorems prog_rep_eq
    
notation Rep_prog ("\<lbrakk>_\<rbrakk>\<^sub>p")

lemma Rep_prog_H1_H3_closed [closure]: "\<lbrakk>P\<rbrakk>\<^sub>p is \<^bold>N"
  using Rep_prog by auto
    
setup_lifting type_definition_prog
    
instantiation prog :: (type) refine
begin
  lift_definition less_eq_prog :: "'a prog \<Rightarrow> 'a prog \<Rightarrow> bool" is
  "op \<le>" .
  lift_definition less_prog :: "'a prog \<Rightarrow> 'a prog \<Rightarrow> bool" is
  "op <" .
  instance by (intro_classes, (transfer, simp add: less_uexpr_def)+)
end

lemma Rep_prog_refine [prog_rep_eq]:
  "P \<sqsubseteq> Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>p \<sqsubseteq> \<lbrakk>Q\<rbrakk>\<^sub>p"
  by (simp add: less_eq_prog.rep_eq)

lemma Rep_prog_eq [prog_rep_eq]:
  "P = Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>p = \<lbrakk>Q\<rbrakk>\<^sub>p"
  by (metis Rep_prog_inverse)

method ptransfer = (simp add: prog_rep_eq)
    
subsection {* Operators *}
  
instantiation prog :: (type) lattice
begin
  lift_definition inf_prog :: "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" is "op \<squnion>" by (simp add: closure)
  lift_definition sup_prog :: "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" is "op \<sqinter>" by (simp add: closure)
instance by (intro_classes; (transfer, rel_simp))
end

instantiation prog :: (type) bounded_lattice
begin
  lift_definition top_prog :: "'\<alpha> prog" is "\<bottom>\<^sub>D" by (simp add: closure)
  lift_definition bot_prog :: "'\<alpha> prog" is "\<top>\<^sub>D" by (simp add: closure)
instance 
  apply (intro_classes; transfer)
  apply (metis H1_below_top Healthy_def)
  apply simp
  done
end
  
abbreviation abort :: "'\<alpha> prog" where "abort \<equiv> \<bottom>"
abbreviation magic :: "'\<alpha> prog" where "magic \<equiv> \<top>"

lift_definition skip     :: "'\<alpha> prog" is "II\<^sub>D" by (simp add: closure)
lift_definition pseq     :: "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" (infix ";" 71) is "op ;;" by (simp add: closure)
lift_definition passigns :: "'\<alpha> usubst \<Rightarrow> '\<alpha> prog" ("\<langle>_\<rangle>\<^sub>p") is "assigns_d" by (simp add: closure)
lift_definition psubst   :: "'\<alpha> usubst \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" is "\<lambda> \<sigma> P. ((\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D) \<oplus>\<^sub>s in\<alpha>) \<dagger> P" by (simp add: closure)
lift_definition paltern  :: "'a set \<Rightarrow> ('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> '\<alpha> prog) \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" is AlternateD by (simp add: closure)
lift_definition paltern_list  :: "('\<alpha> upred \<times> '\<alpha> prog) list \<Rightarrow>  '\<alpha> prog \<Rightarrow> '\<alpha> prog" is AlternateD_list
  by (simp add: AlternateD_list_def list_all_def pred_prod_beta closure)
     (metis AlternateD_H1_H3_closed atLeastLessThan_iff nth_mem)

declare inf_prog.rep_eq [prog_rep_eq]
declare sup_prog.rep_eq [prog_rep_eq]
declare top_prog.rep_eq [prog_rep_eq]
declare bot_prog.rep_eq [prog_rep_eq]
declare skip.rep_eq [prog_rep_eq]
declare pseq.rep_eq [prog_rep_eq]
declare passigns.rep_eq [prog_rep_eq]
declare psubst.rep_eq [prog_rep_eq]
declare paltern.rep_eq [prog_rep_eq]
declare paltern_list.rep_eq [prog_rep_eq]
  
subsection {* Syntax Translations *}
    
adhoc_overloading
  usubst psubst and
  uassigns passigns and
  ualtern paltern and
  ualtern_list paltern_list

translations
  "_assignment xs vs" => "CONST passigns (_mk_usubst (CONST id) xs vs)"
  "x := v" <= "CONST passigns (CONST subst_upd (CONST id) (CONST svar x) v)"
  
subsection {* Proof Tactics *}
  
method pauto   = (ptransfer, rel_auto)
method prefine = (ptransfer, ndes_refine)
method peq     = (ptransfer, ndes_eq)
  
subsection {* Substitution Laws *}
  
lemma psubst_seq [usubst]:
  "\<sigma> \<dagger> (P ; Q) = (\<sigma> \<dagger> P) ; Q"
  by pauto
  
subsection {* Laws of Programming *}
  
theorem skip_left_unit [simp]:
  "skip ; P = P"
  by (transfer, metis H1_idem H1_left_unit Healthy_def')
  
theorem skip_right_unit [simp]:
  "P ; skip = P"
  by (transfer, metis H1_H3_commute H1_idem H3_def Healthy_if)

theorem abort_left_zero [simp]:
  "abort ; P = abort"
  by (transfer, metis H1_idem H1_left_zero Healthy_def')

theorem magic_left_zero [simp]:
  "magic ; P = magic"
  by (transfer, metis H1_idem H1_nok_left_zero Healthy_def')
    
end