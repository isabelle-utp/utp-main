section {* Imperative Programs *}
  
theory utp_prog
  imports "../theories/utp_designs"
begin
  
subsection {* Program Type *}
  
typedef '\<alpha> prog = "{P :: '\<alpha> hrel_des. P is \<^bold>N}"
  by (rule_tac x="true" in exI, simp add: closure)
      
setup_lifting type_definition_prog
    
instantiation prog :: (type) refine
begin
  lift_definition less_eq_prog :: "'a prog \<Rightarrow> 'a prog \<Rightarrow> bool" is
  "op \<le>" .
  lift_definition less_prog :: "'a prog \<Rightarrow> 'a prog \<Rightarrow> bool" is
  "op <" .
  instance by (intro_classes, (transfer, simp add: less_uexpr_def)+)
end
    
subsection {* Operators *}
  
lift_definition abort    :: "'\<alpha> prog" is "true" by (simp add: closure)
lift_definition magic    :: "'\<alpha> prog" is "\<top>\<^sub>D" by (simp add: closure)
lift_definition skip     :: "'\<alpha> prog" is "II\<^sub>D" by (simp add: closure)
lift_definition pseq     :: "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" (infix ";" 71) is "op ;;" by (simp add: closure)
lift_definition passigns :: "'\<alpha> usubst \<Rightarrow> '\<alpha> prog" ("\<langle>_\<rangle>\<^sub>p") is "assigns_d" by (simp add: closure)
lift_definition psubst   :: "'\<alpha> usubst \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" is "\<lambda> \<sigma> P. ((\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D) \<oplus>\<^sub>s in\<alpha>) \<dagger> P" by (simp add: closure)
    
subsection {* Syntax Translations *}
    
adhoc_overloading
  usubst psubst and
  uassigns passigns

translations
  "_assignment xs vs" => "CONST passigns (_mk_usubst (CONST id) xs vs)"
  "x := v" <= "CONST passigns (CONST subst_upd (CONST id) (CONST svar x) v)"

term "x := v"
  
subsection {* Proof Tactic *}
  
method prauto = (transfer, rel_auto)
  
subsection {* Substitution Laws *}
  
lemma psubst_seq [usubst]:
  "\<sigma> \<dagger> (P ; Q) = (\<sigma> \<dagger> P) ; Q"
  by prauto
  
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