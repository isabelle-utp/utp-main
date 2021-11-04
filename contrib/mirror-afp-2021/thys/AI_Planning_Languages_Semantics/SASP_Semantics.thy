theory SASP_Semantics
imports Main
begin

section \<open>Semantics of Fast-Downward's Multi-Valued Planning Tasks Language\<close>

subsection \<open>Syntax\<close>
  type_synonym name = string
  type_synonym ast_variable = "name \<times> nat option \<times> name list" (* var name, axiom layer, atom names *)
  type_synonym ast_variable_section = "ast_variable list"
  type_synonym ast_initial_state = "nat list"
  type_synonym ast_goal = "(nat \<times> nat) list"
  type_synonym ast_precond = "(nat \<times> nat)"
  type_synonym ast_effect = "ast_precond list \<times> nat \<times> nat option \<times> nat"
  type_synonym ast_operator = "name \<times> ast_precond list \<times> ast_effect list \<times> nat"
  type_synonym ast_operator_section = "ast_operator list"
  
  type_synonym ast_problem = 
    "ast_variable_section \<times> ast_initial_state \<times> ast_goal \<times> ast_operator_section"

  type_synonym plan = "name list"
    
  subsubsection \<open>Well-Formedness\<close>
    
  locale ast_problem =
    fixes problem :: ast_problem
  begin    
    definition astDom :: ast_variable_section (* TODO: Dom \<rightarrow> Vars, D \<rightarrow> X*)
      where "astDom \<equiv> case problem of (D,I,G,\<delta>) \<Rightarrow> D"
    definition astI :: ast_initial_state
      where "astI \<equiv> case problem of (D,I,G,\<delta>) \<Rightarrow> I"
    definition astG :: ast_goal
      where "astG \<equiv> case problem of (D,I,G,\<delta>) \<Rightarrow> G"
    definition ast\<delta> :: ast_operator_section
      where "ast\<delta> \<equiv> case problem of (D,I,G,\<delta>) \<Rightarrow> \<delta>"
    
    definition "numVars \<equiv> length astDom"
    definition "numVals x \<equiv> length (snd (snd (astDom!x)))"

    definition "wf_partial_state ps \<equiv> 
        distinct (map fst ps) 
      \<and> (\<forall>(x,v) \<in> set ps. x < numVars \<and> v < numVals x)"
      
    definition wf_operator :: "ast_operator \<Rightarrow> bool" 
      where "wf_operator \<equiv> \<lambda>(name, pres, effs, cost). 
        wf_partial_state pres 
      \<and> distinct (map (\<lambda>(_, v, _, _). v) effs) \<comment> \<open>This may be too restrictive\<close>
      \<and> (\<forall>(epres,x,vp,v)\<in>set effs. 
          wf_partial_state epres 
        \<and> x < numVars \<and> v < numVals x  
        \<and> (case vp of None \<Rightarrow> True | Some v \<Rightarrow> v<numVals x)
        )
    "
      
    definition "well_formed \<equiv> 
      \<comment> \<open>Initial state\<close>
      length astI = numVars
    \<and> (\<forall>x<numVars. astI!x < numVals x)

      \<comment> \<open>Goal\<close>
    \<and> wf_partial_state astG

    \<comment> \<open>Operators\<close>
    \<and> (distinct (map fst ast\<delta>))
    \<and> (\<forall>\<pi>\<in>set ast\<delta>. wf_operator \<pi>)
    "
      
  end  
  
  locale wf_ast_problem = ast_problem +
    assumes wf: well_formed
  begin
    lemma wf_initial: 
      "length astI = numVars" 
      "\<forall>x<numVars. astI!x < numVals x"
      using wf unfolding well_formed_def by auto

    lemma wf_goal: "wf_partial_state astG"    
      using wf unfolding well_formed_def by auto

    lemma wf_operators: 
      "distinct (map fst ast\<delta>)"
      "\<forall>\<pi>\<in>set ast\<delta>. wf_operator \<pi>"
      using wf unfolding well_formed_def by auto
  end      
    
    
  subsection \<open>Semantics as Transition System\<close>  
    
  type_synonym state = "nat \<rightharpoonup> nat"
  type_synonym pstate = "nat \<rightharpoonup> nat"
    
    
  context ast_problem
  begin    
    
    definition Dom :: "nat set" where "Dom = {0..<numVars}"

    definition range_of_var where "range_of_var x \<equiv> {0..<numVals x}"

    definition valid_states :: "state set" where "valid_states \<equiv> {
      s. dom s = Dom \<and> (\<forall>x\<in>Dom. the (s x) \<in> range_of_var x)
    }"

    definition I :: state 
      where "I v \<equiv> if v<length astI then Some (astI!v) else None"

    definition subsuming_states :: "pstate \<Rightarrow> state set"
      where "subsuming_states partial \<equiv> { s\<in>valid_states. partial \<subseteq>\<^sub>m s }"

    definition G :: "state set" 
      where "G \<equiv> subsuming_states (map_of astG)"
end

    definition implicit_pres :: "ast_effect list \<Rightarrow> ast_precond list" where 
      "implicit_pres effs \<equiv> 
      map (\<lambda>(_,v,vpre,_). (v,the vpre))
          (filter (\<lambda>(_,_,vpre,_). vpre\<noteq>None) effs)"

context ast_problem
begin

    definition lookup_operator :: "name \<Rightarrow> ast_operator option" where
      "lookup_operator name \<equiv> find (\<lambda>(n,_,_,_). n=name) ast\<delta>"

    definition enabled :: "name \<Rightarrow> state \<Rightarrow> bool"
      where "enabled name s \<equiv>
        case lookup_operator name of
          Some (_,pres,effs,_) \<Rightarrow> 
              s\<in>subsuming_states (map_of pres)
            \<and> s\<in>subsuming_states (map_of (implicit_pres effs))
        | None \<Rightarrow> False"
      
    definition eff_enabled :: "state \<Rightarrow> ast_effect \<Rightarrow> bool" where
      "eff_enabled s \<equiv> \<lambda>(pres,_,_,_). s\<in>subsuming_states (map_of pres)"

    definition execute :: "name \<Rightarrow> state \<Rightarrow> state" where
      "execute name s \<equiv> 
        case lookup_operator name of
          Some (_,_,effs,_) \<Rightarrow>
            s ++ map_of (map (\<lambda>(_,x,_,v). (x,v)) (filter (eff_enabled s) effs))
        | None \<Rightarrow> undefined                                    
        "

    fun path_to where
      "path_to s [] s' \<longleftrightarrow> s'=s"
    | "path_to s (\<pi>#\<pi>s) s' \<longleftrightarrow> enabled \<pi> s \<and> path_to (execute \<pi> s) \<pi>s s'"

    definition valid_plan :: "plan \<Rightarrow> bool" 
      where "valid_plan \<pi>s \<equiv> \<exists>s'\<in>G. path_to I \<pi>s s'"


  end

  (*
    Next steps:
      * well-formed stuff
      * Executable SAS+ validator (well_formed and execute function)

  *)  
    
  subsubsection \<open>Preservation of well-formedness\<close>  
  context wf_ast_problem 
  begin      
    lemma I_valid: "I \<in> valid_states"
      using wf_initial 
      unfolding valid_states_def Dom_def I_def range_of_var_def
      by (auto split:if_splits)
      
    lemma lookup_operator_wf:
      assumes "lookup_operator name = Some \<pi>"
      shows "wf_operator \<pi>" "fst \<pi> = name"  
    proof -
      obtain name' pres effs cost where [simp]: "\<pi>=(name',pres,effs,cost)" by (cases \<pi>)
      hence [simp]: "name'=name" and IN_AST: "(name,pres,effs,cost) \<in> set ast\<delta>"
        using assms
        unfolding lookup_operator_def
        apply -
        apply (metis (mono_tags, lifting) case_prodD find_Some_iff)  
        by (metis (mono_tags, lifting) case_prodD find_Some_iff nth_mem)  
      
      from IN_AST show WF: "wf_operator \<pi>" "fst \<pi> = name"   
        unfolding enabled_def using wf_operators by auto
    qed
        
        
    lemma execute_preserves_valid:
      assumes "s\<in>valid_states"  
      assumes "enabled name s"  
      shows "execute name s \<in> valid_states"  
    proof -
      from \<open>enabled name s\<close> obtain name' pres effs cost where
        [simp]: "lookup_operator name = Some (name',pres,effs,cost)"
        unfolding enabled_def by (auto split: option.splits)
      from lookup_operator_wf[OF this] have WF: "wf_operator (name,pres,effs,cost)" by simp   
      
      have X1: "s ++ m \<in> valid_states" if "\<forall>x v. m x = Some v \<longrightarrow> x<numVars \<and> v<numVals x" for m
        using that \<open>s\<in>valid_states\<close>
        by (auto 
            simp: valid_states_def Dom_def range_of_var_def map_add_def dom_def 
            split: option.splits)  
      
      have X2: "x<numVars" "v<numVals x" 
        if "map_of (map (\<lambda>(_, x, _, y). (x, y)) (filter (eff_enabled s) effs)) x = Some v"    
        for x v
      proof -
        from that obtain epres vp where "(epres,x,vp,v) \<in> set effs"
          by (auto dest!: map_of_SomeD)
        with WF show "x<numVars" "v<numVals x"
          unfolding wf_operator_def by auto
      qed
          
      show ?thesis
        using assms  
        unfolding enabled_def execute_def 
        by (auto intro!: X1 X2)
    qed      
    
    lemma path_to_pres_valid:
      assumes "s\<in>valid_states"
      assumes "path_to s \<pi>s s'"
      shows "s'\<in>valid_states"
      using assms
      by (induction s \<pi>s s' rule: path_to.induct) (auto simp: execute_preserves_valid)  
      
  end

end
