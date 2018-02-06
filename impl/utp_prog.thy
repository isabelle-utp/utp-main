section {* Imperative Programs *}
  
theory utp_prog
  imports "../theories/designs/utp_designs"
begin
  
subsection {* Program Type *}
  
typedef '\<alpha> prog = "{P :: '\<alpha> hrel_des. P is \<^bold>N}"
  by (rule_tac x="\<bottom>\<^sub>D" in exI, simp add: closure)
    
named_theorems prog_rep_eq and prog_defs
    
notation Rep_prog ("\<lbrakk>_\<rbrakk>\<^sub>p")

lemma Rep_prog_H1_H3_closed [closure]: "\<lbrakk>P\<rbrakk>\<^sub>p is \<^bold>N"
  using Rep_prog by auto
    
lemma Rep_prog_split: "\<lbrakk> \<And> pre post. Q(pre \<turnstile>\<^sub>n post) \<rbrakk> \<Longrightarrow> Q(\<lbrakk>P\<rbrakk>\<^sub>p)"
  by (simp add: Rep_prog_H1_H3_closed ndes_split)
    
lemma Rep_prog_comp [prog_rep_eq]: 
  "(Rep_prog \<circ> (\<lambda> i. P(i))) = (\<lambda> i. \<lbrakk>P(i)\<rbrakk>\<^sub>p)"
  by (auto)
    
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
  apply (simp add: bot_d_true)
  done
end
  
abbreviation abort :: "'\<alpha> prog" where "abort \<equiv> \<bottom>"
abbreviation magic :: "'\<alpha> prog" where "magic \<equiv> \<top>"

lift_definition skip     :: "'\<alpha> prog" is "II\<^sub>D" by (simp add: closure)
lift_definition pseq     :: "'\<alpha> prog \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" (infixr ";" 71) is "op ;;" by (simp add: closure)
lift_definition passigns :: "'\<alpha> usubst \<Rightarrow> '\<alpha> prog" ("\<langle>_\<rangle>\<^sub>p") is "assigns_d" by (simp add: closure)
lift_definition psubst   :: "'\<alpha> usubst \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" is "\<lambda> \<sigma> P. ((\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D) \<oplus>\<^sub>s in\<alpha>) \<dagger> P" by (simp add: closure)
lift_definition paltern  :: "'a set \<Rightarrow> ('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> '\<alpha> prog) \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" is AlternateD by (simp add: closure)
lift_definition paltern_list  :: "('\<alpha> upred \<times> '\<alpha> prog) list \<Rightarrow> '\<alpha> prog \<Rightarrow> '\<alpha> prog" is AlternateD_list
  by (simp add: AlternateD_list_def list_all_def pred_prod_beta closure)
     (metis AlternateD_H1_H3_closed atLeastLessThan_iff nth_mem)  
lift_definition piterate :: "'a set \<Rightarrow> ('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> '\<alpha> prog) \<Rightarrow> '\<alpha> prog" is IterateD by (simp add: closure)
lift_definition piterate_list :: "('\<alpha> upred \<times> '\<alpha> prog) list \<Rightarrow> '\<alpha> prog" is IterateD_list 
  by (simp add: IterateD_list_def list_all_def pred_prod_beta closure)
     (metis IterateD_H1_H3_closed atLeastLessThan_iff nth_mem)
    
lift_definition plocal :: "'a::countable itself \<Rightarrow> (('a \<Longrightarrow> 'b clocal) \<Rightarrow> 'b clocal prog) \<Rightarrow> 'b clocal prog" is
  "\<lambda> t. utp_local_state.var_scope \<L>\<^sub>D['a::countable]" by (simp add: closure)
     
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
declare piterate.rep_eq [prog_rep_eq]
declare piterate_list.rep_eq [prog_rep_eq]
declare plocal.rep_eq [prog_rep_eq]
  
subsection {* Syntax Translations *}
    
adhoc_overloading
  usubst psubst and
  uassigns passigns and
  ualtern paltern and
  ualtern_list paltern_list and
  uiterate piterate and
  uiterate_list piterate_list
  
translations
  "_assignment xs vs" => "CONST passigns (_mk_usubst (CONST id) xs vs)"
  "x := v" <= "CONST passigns (CONST subst_upd (CONST id) (CONST svar x) v)"
  "_altgcomm (_gcomm_show cs)" <= "CONST ualtern_list cs (CONST abort)"
  
no_translations
  "_rel_var_scope x P" => "_var_scope R\<^sub>l x P"
  "_rel_var_scope_type x t P" => "_var_scope_type (_rel_local_state_type t) x t P"

translations
  "var x :: 'a \<bullet> P" == "CONST plocal TYPE('a) (\<lambda> x. P)"
  
subsection {* Proof Tactics *}
  
method pauto   = ((simp add: prog_defs)?, ptransfer, rel_auto)
method prefine = ((simp add: prog_defs)?, ptransfer, ndes_refine)
method peq     = ((simp add: prog_defs)?, ptransfer, ndes_eq)

method prefine' = ((simp add: prog_defs)?, transfer, ndes_refine)
method peq'     = ((simp add: prog_defs)?, transfer, ndes_eq)

subsection {* Substitution Laws *}
  
lemma psubst_seq [usubst]:
  "\<sigma> \<dagger> (P ; Q) = (\<sigma> \<dagger> P) ; Q"
  by pauto
    
lemma psubst_assigns [usubst]:
  "\<sigma> \<dagger> \<langle>\<rho>\<rangle>\<^sub>p = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>p"
  by pauto
    
lemma psubst_binary_altern [usubst]:
  fixes P Q :: "'\<alpha> prog"
  shows "\<sigma> \<dagger> (if b \<rightarrow> P else Q fi) = (if (\<sigma> \<dagger> b) \<rightarrow> (\<sigma> \<dagger> P) else (\<sigma> \<dagger> Q) fi)"
  by (pauto)
    
subsection {* Laws of Programming *}
  
theorem skip_left_unit [simp]:
  "skip ; P = P"
  by (peq')
  
theorem skip_right_unit [simp]:
  "P ; skip = P"
  by (peq')
       
theorem abort_left_zero [simp]:
  "abort ; P = abort"
  by (peq')

theorem magic_left_zero [simp]:
  "magic ; P = magic"
  by (peq')

lemma passigns_comp: "\<langle>\<sigma>\<rangle>\<^sub>p ; P = \<sigma> \<dagger> P"
  by (transfer, rel_blast)
    
end