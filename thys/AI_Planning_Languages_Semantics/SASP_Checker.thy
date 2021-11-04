theory SASP_Checker
imports SASP_Semantics
  "HOL-Library.Code_Target_Nat"
begin

section \<open>An Executable Checker for Multi-Valued Planning Problem Solutions\<close>


  subsection \<open>Auxiliary Lemmas\<close>
  lemma map_of_leI:
    assumes "distinct (map fst l)"
    assumes "\<And>k v. (k,v)\<in>set l \<Longrightarrow> m k = Some v"
    shows "map_of l \<subseteq>\<^sub>m m"  
    using assms
    by (metis (no_types, hide_lams) domIff map_le_def map_of_SomeD not_Some_eq)  

  lemma [simp]: "fst \<circ> (\<lambda>(a, b, c, d). (f a b c d, g a b c d)) = (\<lambda>(a,b,c,d). f a b c d)"
    by auto
      
  lemma map_mp: "m\<subseteq>\<^sub>mm' \<Longrightarrow> m k = Some v \<Longrightarrow> m' k = Some v"    
    by (auto simp: map_le_def dom_def)
      
      
  lemma map_add_map_of_fold: 
    fixes ps and m :: "'a \<rightharpoonup> 'b"
    assumes "distinct (map fst ps)"
    shows "m ++ map_of ps = fold (\<lambda>(k, v) m. m(k \<mapsto> v)) ps m"
  proof -
    have X1: "fold (\<lambda>(k, v) m. m(k \<mapsto> v)) ps m(a \<mapsto> b) 
            = fold (\<lambda>(k, v) m. m(k \<mapsto> v)) ps (m(a \<mapsto> b))" 
      if "a \<notin> fst ` set ps"
      for a b ps and m :: "'a \<rightharpoonup> 'b"
      using that
      by (induction ps arbitrary: m) (auto simp: fun_upd_twist)
    
    show ?thesis
      using assms
      by (induction ps arbitrary: m) (auto simp: X1)
  qed    

  

  subsection \<open>Well-formedness Check\<close>
  lemmas wf_code_thms = 
      ast_problem.astDom_def ast_problem.astI_def ast_problem.astG_def ast_problem.ast\<delta>_def
      ast_problem.numVars_def ast_problem.numVals_def 
      ast_problem.wf_partial_state_def ast_problem.wf_operator_def ast_problem.well_formed_def
      
      
  declare wf_code_thms[code]
      
  export_code ast_problem.well_formed in SML

    
  subsection \<open>Execution\<close>  
    
  definition match_pre :: "ast_precond \<Rightarrow> state \<Rightarrow> bool" where
    "match_pre \<equiv> \<lambda>(x,v) s. s x = Some v"
    
  definition match_pres :: "ast_precond list \<Rightarrow> state \<Rightarrow> bool" where 
    "match_pres pres s \<equiv> \<forall>pre\<in>set pres. match_pre pre s"
    
  definition match_implicit_pres :: "ast_effect list \<Rightarrow> state \<Rightarrow> bool" where
    "match_implicit_pres effs s \<equiv> \<forall>(_,x,vp,_)\<in>set effs. 
      (case vp of None \<Rightarrow> True | Some v \<Rightarrow> s x = Some v)"
    
  definition enabled_opr' :: "ast_operator \<Rightarrow> state \<Rightarrow> bool" where 
    "enabled_opr' \<equiv> \<lambda>(name,pres,effs,cost) s. match_pres pres s \<and> match_implicit_pres effs s"
      
  definition eff_enabled' :: "state \<Rightarrow> ast_effect \<Rightarrow> bool" where
    "eff_enabled' s \<equiv> \<lambda>(pres,_,_,_). match_pres pres s"
    
  definition "execute_opr' \<equiv> \<lambda>(name,_,effs,_) s. 
    let effs = filter (eff_enabled' s) effs
    in fold (\<lambda>(_,x,_,v) s. s(x\<mapsto>v)) effs s
  "  

  definition lookup_operator' :: "ast_problem \<Rightarrow> name \<rightharpoonup> ast_operator" 
    where "lookup_operator' \<equiv> \<lambda>(D,I,G,\<delta>) name. find (\<lambda>(n,_,_,_). n=name) \<delta>"
    
  definition enabled' :: "ast_problem \<Rightarrow> name \<Rightarrow> state \<Rightarrow> bool" where
    "enabled' problem name s \<equiv> 
      case lookup_operator' problem name of 
        Some \<pi> \<Rightarrow> enabled_opr' \<pi> s
      | None \<Rightarrow> False"

  definition execute' :: "ast_problem \<Rightarrow> name \<Rightarrow> state \<Rightarrow> state" where
    "execute' problem name s \<equiv> 
      case lookup_operator' problem name of 
        Some \<pi> \<Rightarrow> execute_opr' \<pi> s
      | None \<Rightarrow> undefined"
    
    
  context wf_ast_problem begin  
    
    lemma match_pres_correct:
      assumes D: "distinct (map fst pres)"
      assumes "s\<in>valid_states"  
      shows "match_pres pres s \<longleftrightarrow> s\<in>subsuming_states (map_of pres)"
    proof -
      have "match_pres pres s \<longleftrightarrow> map_of pres \<subseteq>\<^sub>m s"
        unfolding match_pres_def match_pre_def
        apply (auto split: prod.splits)
        using map_le_def map_of_SomeD apply fastforce  
        by (metis (full_types) D domIff map_le_def map_of_eq_Some_iff option.simps(3))
    
      with assms show ?thesis          
        unfolding subsuming_states_def 
        by auto
    qed
       
    lemma match_implicit_pres_correct:
      assumes D: "distinct (map (\<lambda>(_, v, _, _). v) effs)"
      assumes "s\<in>valid_states"  
      shows "match_implicit_pres effs s \<longleftrightarrow> s\<in>subsuming_states (map_of (implicit_pres effs))"
    proof -
      from assms show ?thesis
        unfolding subsuming_states_def 
        unfolding match_implicit_pres_def implicit_pres_def
        apply (auto 
            split: prod.splits option.splits 
            simp: distinct_map_filter
            intro!: map_of_leI)
        apply (force simp: distinct_map_filter split: prod.split elim: map_mp)  
        done  
    qed
          
    lemma enabled_opr'_correct:
      assumes V: "s\<in>valid_states"
      assumes "lookup_operator name = Some \<pi>"  
      shows "enabled_opr' \<pi> s \<longleftrightarrow> enabled name s"  
      using lookup_operator_wf[OF assms(2)] assms
      unfolding enabled_opr'_def enabled_def wf_operator_def
      by (auto 
          simp: match_pres_correct[OF _ V] match_implicit_pres_correct[OF _ V]
          simp: wf_partial_state_def
          split: option.split
          )  
       
    lemma eff_enabled'_correct:
      assumes V: "s\<in>valid_states"
      assumes "case eff of (pres,_,_,_) \<Rightarrow> wf_partial_state pres"  
      shows "eff_enabled' s eff \<longleftrightarrow> eff_enabled s eff"  
      using assms  
      unfolding eff_enabled'_def eff_enabled_def wf_partial_state_def
      by (auto simp: match_pres_correct)  
    
    
    lemma execute_opr'_correct:
      assumes V: "s\<in>valid_states"
      assumes LO: "lookup_operator name = Some \<pi>"  
      shows "execute_opr' \<pi> s = execute name s"  
    proof (cases \<pi>)
      case [simp]: (fields name pres effs)
        
      have [simp]: "filter (eff_enabled' s) effs = filter (eff_enabled s) effs"  
        apply (rule filter_cong[OF refl])
        apply (rule eff_enabled'_correct[OF V])
        using lookup_operator_wf[OF LO]  
        unfolding wf_operator_def by auto  
          
      have X1: "distinct (map fst (map (\<lambda>(_, x, _, y). (x, y)) (filter (eff_enabled s) effs)))"
        using lookup_operator_wf[OF LO]
        unfolding wf_operator_def 
        by (auto simp: distinct_map_filter)
        
      term "filter (eff_enabled s) effs"    
          
      have [simp]: 
        "fold (\<lambda>(_, x, _, v) s. s(x \<mapsto> v)) l s =
         fold (\<lambda>(k, v) m. m(k \<mapsto> v)) (map (\<lambda>(_, x, _, y). (x, y)) l) s" 
        for l :: "ast_effect list"
        by (induction l arbitrary: s) auto
          
      show ?thesis 
        unfolding execute_opr'_def execute_def using LO
        by (auto simp: map_add_map_of_fold[OF X1])
    qed
        
      
    lemma lookup_operator'_correct: 
      "lookup_operator' problem name = lookup_operator name"
      unfolding lookup_operator'_def lookup_operator_def
      unfolding ast\<delta>_def  
      by (auto split: prod.split)  
        
    lemma enabled'_correct:
      assumes V: "s\<in>valid_states"
      shows "enabled' problem name s = enabled name s"
      unfolding enabled'_def  
      using enabled_opr'_correct[OF V]
      by (auto split: option.splits simp: enabled_def lookup_operator'_correct)  
        
    lemma execute'_correct:
      assumes V: "s\<in>valid_states"
      assumes "enabled name s"      (* Intentionally put this here, also we could resolve non-enabled case by reflexivity (undefined=undefined) *)
      shows "execute' problem name s = execute name s"  
      unfolding execute'_def  
      using execute_opr'_correct[OF V] \<open>enabled name s\<close>
      by (auto split: option.splits simp: enabled_def lookup_operator'_correct)  
        
        
        
  end    

  context ast_problem 
  begin  
    
    fun simulate_plan :: "plan \<Rightarrow> state \<rightharpoonup> state" where
      "simulate_plan [] s = Some s"
    | "simulate_plan (\<pi>#\<pi>s) s = (
        if enabled \<pi> s then 
          let s' = execute \<pi> s in
          simulate_plan \<pi>s s'
        else
          None
      )"  
    
    lemma simulate_plan_correct: "simulate_plan \<pi>s s = Some s' \<longleftrightarrow> path_to s \<pi>s s'"
      by (induction s \<pi>s s' rule: path_to.induct) auto  
      
    definition check_plan :: "plan \<Rightarrow> bool" where
      "check_plan \<pi>s = (
        case simulate_plan \<pi>s I of 
          None \<Rightarrow> False 
        | Some s' \<Rightarrow> s' \<in> G)"
      
    lemma check_plan_correct: "check_plan \<pi>s \<longleftrightarrow> valid_plan \<pi>s"
      unfolding check_plan_def valid_plan_def 
      by (auto split: option.split simp: simulate_plan_correct[symmetric])
      
  end  
    
  fun simulate_plan' :: "ast_problem \<Rightarrow> plan \<Rightarrow> state \<rightharpoonup> state" where
    "simulate_plan' problem [] s = Some s"
  | "simulate_plan' problem (\<pi>#\<pi>s) s = (
      if enabled' problem \<pi> s then
        let s = execute' problem \<pi> s in
        simulate_plan' problem \<pi>s s
      else
        None
    )"  
    
  text \<open>Avoiding duplicate lookup.\<close>
  (*[code]  *)  
  lemma simulate_plan'_code[code]:
    "simulate_plan' problem [] s = Some s"
    "simulate_plan' problem (\<pi>#\<pi>s) s = (
      case lookup_operator' problem \<pi> of
        None \<Rightarrow> None
      | Some \<pi> \<Rightarrow> 
          if enabled_opr' \<pi> s then 
            simulate_plan' problem \<pi>s (execute_opr' \<pi> s)
          else None
    )"
    by (auto simp: enabled'_def execute'_def split: option.split)
    
    
  definition initial_state' :: "ast_problem \<Rightarrow> state" where
    "initial_state' problem \<equiv> let astI = ast_problem.astI problem in (
       \<lambda>v. if v<length astI then Some (astI!v) else None
     )"
      
  definition check_plan' :: "ast_problem \<Rightarrow> plan \<Rightarrow> bool" where
    "check_plan' problem \<pi>s = (
      case simulate_plan' problem \<pi>s (initial_state' problem) of 
        None \<Rightarrow> False 
      | Some s' \<Rightarrow> match_pres (ast_problem.astG problem) s')"
      
      
  context wf_ast_problem 
  begin  
    
    lemma simulate_plan'_correct:
      assumes "s\<in>valid_states"
      shows "simulate_plan' problem \<pi>s s = simulate_plan \<pi>s s"
      using assms
      apply (induction \<pi>s s rule: simulate_plan.induct)
      apply (auto simp: enabled'_correct execute'_correct execute_preserves_valid)  
      done
        
    lemma simulate_plan'_correct_paper: (* For presentation in paper. 
        Summarizing intermediate refinement step. *)
      assumes "s\<in>valid_states"
      shows "simulate_plan' problem \<pi>s s = Some s'
            \<longleftrightarrow> path_to s \<pi>s s'"
      using simulate_plan'_correct[OF assms] simulate_plan_correct by simp
      
        
    lemma initial_state'_correct: 
      "initial_state' problem = I"
      unfolding initial_state'_def I_def by (auto simp: Let_def)

    lemma check_plan'_correct:
      "check_plan' problem \<pi>s = check_plan \<pi>s"
    proof -
      have D: "distinct (map fst astG)" using wf_goal unfolding wf_partial_state_def by auto 
        
      have S'V: "s'\<in>valid_states" if "simulate_plan \<pi>s I = Some s'" for s'
        using that by (auto simp: simulate_plan_correct path_to_pres_valid[OF I_valid])
          
      show ?thesis
        unfolding check_plan'_def check_plan_def
        by (auto 
            split: option.splits 
            simp: initial_state'_correct simulate_plan'_correct[OF I_valid]
            simp: match_pres_correct[OF D S'V] G_def
            )
    qed  
        
  end

    
  (* Overall checker *)  
    
  definition verify_plan :: "ast_problem \<Rightarrow> plan \<Rightarrow> String.literal + unit" where
    "verify_plan problem \<pi>s = (
      if ast_problem.well_formed problem then
        if check_plan' problem \<pi>s then Inr () else Inl (STR ''Invalid plan'')
      else Inl (STR ''Problem not well formed'')
    )"

  lemma verify_plan_correct:
    "verify_plan problem \<pi>s = Inr () 
    \<longleftrightarrow> ast_problem.well_formed problem \<and> ast_problem.valid_plan problem \<pi>s"
  proof -
    {
      assume "ast_problem.well_formed problem"
      then interpret wf_ast_problem by unfold_locales
          
      from check_plan'_correct check_plan_correct 
      have "check_plan' problem \<pi>s = valid_plan \<pi>s" by simp
    } 
    then show ?thesis  
      unfolding verify_plan_def
      by auto  
  qed

  definition nat_opt_of_integer :: "integer \<Rightarrow> nat option" where
       "nat_opt_of_integer i = (if (i \<ge> 0) then Some (nat_of_integer i) else None)"

  (*Export functions, which includes constructors*)
  export_code verify_plan nat_of_integer integer_of_nat nat_opt_of_integer Inl Inr String.explode String.implode
    in SML
    module_name SASP_Checker_Exported
    file "code/SASP_Checker_Exported.sml"

end
