(*
  Author: Mohammad Abdulaziz
*)
theory AST_SAS_Plus_Equivalence
  imports "AI_Planning_Languages_Semantics.SASP_Semantics" "SAS_Plus_Semantics" "List-Index.List_Index" 
begin                                                               

section \<open>Proving Equivalence of SAS+ representation and Fast-Downward's Multi-Valued Problem
         Representation\<close>

subsection \<open>Translating Fast-Downward's represnetation to SAS+\<close>


type_synonym nat_sas_plus_problem = "(nat, nat) sas_plus_problem" 
type_synonym nat_sas_plus_operator = "(nat, nat) sas_plus_operator" 
type_synonym nat_sas_plus_plan = "(nat, nat) sas_plus_plan" 
type_synonym nat_sas_plus_state = "(nat, nat) state" 


definition is_standard_effect :: "ast_effect \<Rightarrow> bool"
  where "is_standard_effect \<equiv> \<lambda>(pre, _, _, _). pre = []" 

definition is_standard_operator :: "ast_operator \<Rightarrow> bool"
  where "is_standard_operator \<equiv> \<lambda>(_, _, effects, _). list_all is_standard_effect effects"

fun rem_effect_implicit_pres:: "ast_effect \<Rightarrow> ast_effect" where
  "rem_effect_implicit_pres (preconds, v, implicit_pre, eff) = (preconds, v, None, eff)" 

fun rem_implicit_pres :: "ast_operator \<Rightarrow> ast_operator" where
  "rem_implicit_pres (name, preconds, effects, cost) =
     (name, (implicit_pres effects) @ preconds, map rem_effect_implicit_pres effects, cost)"

fun rem_implicit_pres_ops :: "ast_problem \<Rightarrow> ast_problem" where
  "rem_implicit_pres_ops (vars, init, goal, ops) = (vars, init, goal, map rem_implicit_pres ops)"

definition "consistent_map_lists xs1 xs2 \<equiv> (\<forall>(x1,x2) \<in> set xs1. \<forall>(y1,y2)\<in> set xs2. x1 = y1 \<longrightarrow> x1 = y2)"

lemma map_add_comm: "(\<And>x. x \<in> dom m1 \<and> x \<in> dom m2 \<Longrightarrow> m1 x = m2 x) \<Longrightarrow> m1 ++ m2 = m2 ++ m1"
  by (fastforce simp add: map_add_def split: option.splits)

lemma first_map_add_submap: "(\<And>x. x \<in> dom m1 \<and> x \<in> dom m2 \<Longrightarrow> m1 x = m2 x) \<Longrightarrow>
        m1 ++ m2 \<subseteq>\<^sub>m x \<Longrightarrow> m1 \<subseteq>\<^sub>m x"
  using map_add_le_mapE map_add_comm
  by force

lemma subsuming_states_map_add:
  "(\<And>x. x \<in> dom m1 \<inter> dom m2 \<Longrightarrow> m1 x = m2 x) \<Longrightarrow>
  m1 ++ m2 \<subseteq>\<^sub>m s \<longleftrightarrow> (m1 \<subseteq>\<^sub>m s \<and> m2 \<subseteq>\<^sub>m s)"
  by(auto simp: map_add_le_mapI intro: first_map_add_submap map_add_le_mapE)

lemma consistent_map_lists:
  "\<lbrakk>distinct (map fst (xs1 @ xs2)); x \<in> dom (map_of xs1) \<inter> dom (map_of xs2)\<rbrakk> \<Longrightarrow> 
     (map_of xs1) x = (map_of xs2) x"
  apply(induction xs1)
   apply (simp_all add: consistent_map_lists_def image_def)
  using map_of_SomeD
  by fastforce

lemma subsuming_states_append: 
  "distinct (map fst (xs @ ys)) \<Longrightarrow> 
     (map_of (xs @ ys)) \<subseteq>\<^sub>m s \<longleftrightarrow> ((map_of ys) \<subseteq>\<^sub>m s \<and> (map_of xs) \<subseteq>\<^sub>m s)"
  unfolding map_of_append
  apply(intro subsuming_states_map_add)
  apply (auto simp add: image_def)
  by (metis (mono_tags, lifting) IntI empty_iff fst_conv mem_Collect_eq)

definition consistent_pres_op where
  "consistent_pres_op op \<equiv> (case op of (name, pres, effs, cost) \<Rightarrow> 
                               distinct (map fst (pres @ (implicit_pres effs)))
                               \<and> consistent_map_lists pres (implicit_pres effs))"

definition consistent_pres_op' where
  "consistent_pres_op' op \<equiv> (case op of (name, pres, effs, cost) \<Rightarrow> 
                               consistent_map_lists pres (implicit_pres effs))"

lemma consistent_pres_op_then': "consistent_pres_op op \<Longrightarrow> consistent_pres_op' op"
  by(auto simp add: consistent_pres_op'_def consistent_pres_op_def)

lemma rem_implicit_pres_ops_valid_states:
   "ast_problem.valid_states (rem_implicit_pres_ops prob) = ast_problem.valid_states prob"
  apply(cases prob)
  by(auto simp add: ast_problem.valid_states_def ast_problem.Dom_def 
                       ast_problem.numVars_def ast_problem.astDom_def
                       ast_problem.range_of_var_def ast_problem.numVals_def)

lemma rem_implicit_pres_ops_lookup_op_None:
  "ast_problem.lookup_operator (vars, init, goal, ops) name = None \<longleftrightarrow> 
   ast_problem.lookup_operator (rem_implicit_pres_ops (vars, init, goal, ops)) name = None"
  by (induction ops) (auto simp: ast_problem.lookup_operator_def ast_problem.ast\<delta>_def)

lemma rem_implicit_pres_ops_lookup_op_Some_1:
  "ast_problem.lookup_operator (vars, init, goal, ops) name = Some (n,p,vp,e) \<Longrightarrow>
   ast_problem.lookup_operator (rem_implicit_pres_ops (vars, init, goal, ops)) name =
     Some (rem_implicit_pres (n,p,vp,e))"
  by (induction ops) (fastforce simp: ast_problem.lookup_operator_def ast_problem.ast\<delta>_def)+

lemma rem_implicit_pres_ops_lookup_op_Some_1':
  "ast_problem.lookup_operator prob name = Some (n,p,vp,e) \<Longrightarrow>
   ast_problem.lookup_operator (rem_implicit_pres_ops prob) name =
     Some (rem_implicit_pres (n,p,vp,e))"
  apply(cases prob)
  using rem_implicit_pres_ops_lookup_op_Some_1
  by simp

lemma implicit_pres_empty: "implicit_pres (map rem_effect_implicit_pres effs) = []"
  by (induction effs) (auto simp: implicit_pres_def)

lemma rem_implicit_pres_ops_lookup_op_Some_2:
  "ast_problem.lookup_operator (rem_implicit_pres_ops (vars, init, goal, ops)) name = Some op
     \<Longrightarrow> \<exists>op'. ast_problem.lookup_operator (vars, init, goal, ops) name = Some op' \<and>
               (op = rem_implicit_pres op')"
  by (induction ops) (auto simp: ast_problem.lookup_operator_def ast_problem.ast\<delta>_def implicit_pres_empty image_def)

lemma rem_implicit_pres_ops_lookup_op_Some_2':
  "ast_problem.lookup_operator (rem_implicit_pres_ops prob) name = Some (n,p,e,c)
     \<Longrightarrow> \<exists>op'. ast_problem.lookup_operator prob name = Some op' \<and>
               ((n,p,e,c) = rem_implicit_pres op')"
  apply(cases prob)
  using rem_implicit_pres_ops_lookup_op_Some_2
  by auto

lemma subsuming_states_def':
  "s \<in> ast_problem.subsuming_states prob ps = (s \<in> (ast_problem.valid_states prob) \<and> ps \<subseteq>\<^sub>m s)"
  by (auto simp add: ast_problem.subsuming_states_def)

lemma rem_implicit_pres_ops_enabled_1:
  "\<lbrakk>(\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> consistent_pres_op op);
        ast_problem.enabled prob name s\<rbrakk> \<Longrightarrow>
     ast_problem.enabled (rem_implicit_pres_ops prob) name s"
  by (fastforce simp: ast_problem.enabled_def rem_implicit_pres_ops_valid_states subsuming_states_def'
                      implicit_pres_empty
                 intro!: map_add_le_mapI
                 dest: rem_implicit_pres_ops_lookup_op_Some_1'
                 split: option.splits)+

context ast_problem
begin

lemma lookup_Some_in\<delta>: "lookup_operator \<pi> = Some op \<Longrightarrow> op\<in>set ast\<delta>"
    by(auto simp: find_Some_iff in_set_conv_nth lookup_operator_def)

end

lemma rem_implicit_pres_ops_enabled_2:
  assumes "(\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> consistent_pres_op op)"
  shows "ast_problem.enabled (rem_implicit_pres_ops prob) name s \<Longrightarrow> 
           ast_problem.enabled prob name s"
  using assms[OF ast_problem.lookup_Some_in\<delta>, unfolded consistent_pres_op_def]
  apply(auto simp: subsuming_states_append rem_implicit_pres_ops_valid_states subsuming_states_def'
                   ast_problem.enabled_def
             dest!: rem_implicit_pres_ops_lookup_op_Some_2'
             split: option.splits)
  using subsuming_states_map_add consistent_map_lists
  apply (metis Map.map_add_comm dom_map_of_conv_image_fst map_add_le_mapE)
  using map_add_le_mapE by blast

lemma rem_implicit_pres_ops_enabled:
  "(\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> consistent_pres_op op) \<Longrightarrow>
        ast_problem.enabled (rem_implicit_pres_ops prob) name s = ast_problem.enabled prob name s"
  using rem_implicit_pres_ops_enabled_1 rem_implicit_pres_ops_enabled_2
  by blast

context ast_problem
begin

lemma std_eff_enabled[simp]:
  "is_standard_operator (name, pres, effs, layer) \<Longrightarrow> s \<in> valid_states \<Longrightarrow> (filter (eff_enabled s) effs) = effs"
  by (induction effs) (auto simp: is_standard_operator_def is_standard_effect_def eff_enabled_def subsuming_states_def)

end

lemma is_standard_operator_rem_implicit: "is_standard_operator (n,p,vp,v) \<Longrightarrow> 
         is_standard_operator (rem_implicit_pres (n,p,vp,v))"
  by (induction vp) (auto simp: is_standard_operator_def is_standard_effect_def)

lemma is_standard_operator_rem_implicit_pres_ops:
   "\<lbrakk>(\<And>op. op \<in> set (ast_problem.ast\<delta> (a,b,c,d)) \<Longrightarrow> is_standard_operator op);
       op \<in> set (ast_problem.ast\<delta> (rem_implicit_pres_ops (a,b,c,d)))\<rbrakk>
       \<Longrightarrow> is_standard_operator op"
  by (induction d) (fastforce simp add: ast_problem.ast\<delta>_def image_def dest!: is_standard_operator_rem_implicit)+

lemma is_standard_operator_rem_implicit_pres_ops':
   "\<lbrakk>op \<in> set (ast_problem.ast\<delta> (rem_implicit_pres_ops prob));
    (\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> is_standard_operator op)\<rbrakk>
      \<Longrightarrow> is_standard_operator op"
  apply(cases prob)
  using is_standard_operator_rem_implicit_pres_ops
  by blast

lemma in_rem_implicit_pres_\<delta>:
  "op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow>
     rem_implicit_pres op \<in> set (ast_problem.ast\<delta> (rem_implicit_pres_ops prob))"
  by(auto simp add: ast_problem.ast\<delta>_def)

lemma rem_implicit_pres_ops_execute:
  assumes
    "(\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> is_standard_operator op)" and
    "s \<in> ast_problem.valid_states prob"
  shows "ast_problem.execute (rem_implicit_pres_ops prob) name s = ast_problem.execute prob name s"
proof-
  have "(n,ps,es,c) \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow>
       (filter (ast_problem.eff_enabled prob s) es) = es" for n ps es c
    using assms(2)
    by (auto simp add: ast_problem.std_eff_enabled dest!: assms(1))
  moreover have "(n,ps,es,c) \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow>
       (filter (ast_problem.eff_enabled (rem_implicit_pres_ops prob) s) (map rem_effect_implicit_pres es))
            = map rem_effect_implicit_pres es" for n ps es c
    using assms
    by (fastforce simp add: ast_problem.std_eff_enabled rem_implicit_pres_ops_valid_states
        dest!: is_standard_operator_rem_implicit_pres_ops'
        dest: in_rem_implicit_pres_\<delta>)
  moreover have "map_of (map ((\<lambda>(_,x,_,v). (x,v)) o rem_effect_implicit_pres) effs) =
                    map_of (map (\<lambda>(_,x,_,v). (x,v)) effs)" for effs
    by (induction effs) auto
  ultimately show ?thesis
    by(auto simp add: ast_problem.execute_def rem_implicit_pres_ops_lookup_op_Some_1'
        split: option.splits
        dest: rem_implicit_pres_ops_lookup_op_Some_2' ast_problem.lookup_Some_in\<delta>)
qed

lemma rem_implicit_pres_ops_path_to:
   "wf_ast_problem prob \<Longrightarrow>
       (\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> consistent_pres_op op) \<Longrightarrow>
       (\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> is_standard_operator op) \<Longrightarrow>
       s \<in> ast_problem.valid_states prob \<Longrightarrow>
       ast_problem.path_to (rem_implicit_pres_ops prob) s \<pi>s s' = ast_problem.path_to prob s \<pi>s s'"
  by (induction \<pi>s arbitrary: s)
     (auto simp: rem_implicit_pres_ops_execute rem_implicit_pres_ops_enabled
                 ast_problem.path_to.simps wf_ast_problem.execute_preserves_valid)

lemma rem_implicit_pres_ops_astG[simp]: "ast_problem.astG (rem_implicit_pres_ops prob) =
           ast_problem.astG prob"
  apply(cases prob)
  by (auto simp add: ast_problem.astG_def)

lemma rem_implicit_pres_ops_goal[simp]: "ast_problem.G (rem_implicit_pres_ops prob) = ast_problem.G prob"
  apply(cases prob)
  using rem_implicit_pres_ops_valid_states
  by (auto simp add: ast_problem.G_def ast_problem.astG_def subsuming_states_def')

lemma rem_implicit_pres_ops_astI[simp]:
   "ast_problem.astI (rem_implicit_pres_ops prob) = ast_problem.astI prob"
  apply(cases prob)
  by (auto simp add: ast_problem.I_def ast_problem.astI_def subsuming_states_def')

lemma rem_implicit_pres_ops_init[simp]: "ast_problem.I (rem_implicit_pres_ops prob) = ast_problem.I prob"
  apply(cases prob)
  by (auto simp add: ast_problem.I_def ast_problem.astI_def)

lemma rem_implicit_pres_ops_valid_plan:
  assumes "wf_ast_problem prob"
       "(\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> consistent_pres_op op)"
       "(\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> is_standard_operator op)"
  shows "ast_problem.valid_plan (rem_implicit_pres_ops prob) \<pi>s = ast_problem.valid_plan prob \<pi>s"
  using wf_ast_problem.I_valid[OF assms(1)] rem_implicit_pres_ops_path_to[OF assms]
  by (simp add: ast_problem.valid_plan_def rem_implicit_pres_ops_goal rem_implicit_pres_ops_init)

lemma rem_implicit_pres_ops_numVars[simp]:
  "ast_problem.numVars (rem_implicit_pres_ops prob) = ast_problem.numVars prob"
  by (cases prob) (simp add: ast_problem.numVars_def ast_problem.astDom_def)

lemma rem_implicit_pres_ops_numVals[simp]:
  "ast_problem.numVals (rem_implicit_pres_ops prob) x = ast_problem.numVals prob x"
  by (cases prob) (simp add: ast_problem.numVals_def ast_problem.astDom_def)

lemma in_implicit_pres: 
  "(x, a) \<in> set (implicit_pres effs) \<Longrightarrow> (\<exists>epres v vp. (epres,x,vp,v)\<in> set effs \<and> vp = Some a)"
  by (induction effs) (fastforce simp: implicit_pres_def image_def split: if_splits)+

lemma pair4_eqD: "(a1,a2,a3,a4) = (b1,b2,b3,b4) \<Longrightarrow> a3 = b3"
  by simp  

lemma rem_implicit_pres_ops_wf_partial_state:
   "ast_problem.wf_partial_state (rem_implicit_pres_ops prob) s =
         ast_problem.wf_partial_state prob s"
  by (auto simp: ast_problem.wf_partial_state_def)

lemma rem_implicit_pres_wf_operator:
  assumes "consistent_pres_op op"
    "ast_problem.wf_operator prob op"
  shows
    "ast_problem.wf_operator (rem_implicit_pres_ops prob) (rem_implicit_pres op)"
proof-
  obtain name pres effs cost where op: "op = (name, pres, effs, cost)"
    by (cases op)
  hence asses: "consistent_pres_op (name, pres, effs, cost)"
    "ast_problem.wf_operator prob (name, pres, effs, cost)"
    using assms
    by auto
  hence "distinct (map fst ((implicit_pres effs) @ pres))"
    by (simp only: consistent_pres_op_def) auto
  moreover have "x < ast_problem.numVars (rem_implicit_pres_ops prob)"
    "v < ast_problem.numVals (rem_implicit_pres_ops prob) x"
    if "(x,v) \<in> set ((implicit_pres effs) @ pres)" for x v
    using that asses
    by (auto dest!: in_implicit_pres simp: ast_problem.wf_partial_state_def ast_problem.wf_operator_def)
  ultimately have "ast_problem.wf_partial_state (rem_implicit_pres_ops prob) ((implicit_pres effs) @ pres)"
    by (auto simp only: ast_problem.wf_partial_state_def)
  moreover have "(map (\<lambda>(_, v, _, _). v) effs) = 
                        (map (\<lambda>(_, v, _, _). v) (map rem_effect_implicit_pres effs))"
    by auto
  hence "distinct (map (\<lambda>(_, v, _, _). v) (map rem_effect_implicit_pres effs))"
    using assms(2)
    by (auto simp only: op ast_problem.wf_operator_def rem_implicit_pres.simps dest!: pair4_eqD)
  moreover have "(\<exists>vp. (epres,x,vp,v)\<in>set effs) \<longleftrightarrow> (epres,x,None,v)\<in>set (map rem_effect_implicit_pres effs)"
    for epres x v
    by force
  ultimately show ?thesis
    using assms(2)
    by (auto simp: op ast_problem.wf_operator_def rem_implicit_pres_ops_wf_partial_state 
             split: prod.splits)      
qed

lemma rem_implicit_pres_ops_in\<delta>D: "op \<in> set (ast_problem.ast\<delta> (rem_implicit_pres_ops prob))
        \<Longrightarrow> (\<exists>op'. op' \<in> set (ast_problem.ast\<delta> prob) \<and> op = rem_implicit_pres op')"
  by (cases prob) (force simp: ast_problem.ast\<delta>_def)

lemma rem_implicit_pres_ops_well_formed:
  assumes "(\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> consistent_pres_op op)"
        "ast_problem.well_formed prob"
  shows "ast_problem.well_formed (rem_implicit_pres_ops prob)"
proof-
  have "map fst (ast_problem.ast\<delta> (rem_implicit_pres_ops prob)) = map fst (ast_problem.ast\<delta> prob)"
    by (cases prob) (auto simp: ast_problem.ast\<delta>_def)
  thus ?thesis
   using assms
   by(auto simp add: ast_problem.well_formed_def rem_implicit_pres_ops_wf_partial_state
           simp del: rem_implicit_pres.simps
           dest!: rem_implicit_pres_ops_in\<delta>D
           intro!: rem_implicit_pres_wf_operator)
qed

definition is_standard_effect'
  :: "ast_effect \<Rightarrow> bool"
  where "is_standard_effect' \<equiv> \<lambda>(pre, _, vpre, _). pre = [] \<and> vpre = None" 

definition is_standard_operator'
  :: "ast_operator \<Rightarrow> bool"
  where "is_standard_operator' \<equiv> \<lambda>(_, _, effects, _). list_all is_standard_effect' effects"

lemma rem_implicit_pres_is_standard_operator':
  "is_standard_operator (n,p,es,c) \<Longrightarrow> is_standard_operator' (rem_implicit_pres (n,p,es,c))"
  by (induction es) (auto simp: is_standard_operator'_def is_standard_operator_def is_standard_effect_def
                                is_standard_effect'_def)

lemma rem_implicit_pres_ops_is_standard_operator':
  "(\<And>op. op \<in> set (ast_problem.ast\<delta> (vs, I, G, ops)) \<Longrightarrow> is_standard_operator op) \<Longrightarrow>
    \<pi>\<in>set (ast_problem.ast\<delta> (rem_implicit_pres_ops (vs, I, G, ops))) \<Longrightarrow> is_standard_operator' \<pi>"
  by (cases ops) (auto simp: ast_problem.ast\<delta>_def dest!: rem_implicit_pres_is_standard_operator')

locale abs_ast_prob = wf_ast_problem + 
  assumes no_cond_effs: "\<forall>\<pi>\<in>set ast\<delta>. is_standard_operator' \<pi>"

context ast_problem
begin

definition "abs_ast_variable_section = [0..<(length astDom)]"

definition abs_range_map
  :: "(nat \<rightharpoonup> nat list)"
  where "abs_range_map \<equiv> 
        map_of (zip abs_ast_variable_section 
                    (map ((\<lambda>vals. [0..<length vals]) o snd o snd)
                         astDom))"

end

context abs_ast_prob
begin
      
lemma is_valid_vars_1: "astDom \<noteq> [] \<Longrightarrow> abs_ast_variable_section \<noteq> []"
  by(simp add: abs_ast_variable_section_def)

end

lemma upt_eq_Nil_conv'[simp]: "([] = [i..<j]) = (j = 0 \<or> j \<le> i)"
  by(induct j)simp_all

lemma map_of_zip_map_Some: 
     "v < length xs
        \<Longrightarrow> (map_of (zip [0..<length xs] (map f xs)) v) = Some (f (xs ! v))"
  by (induction xs rule: rev_induct) (auto simp add: nth_append map_add_Some_iff)

lemma map_of_zip_Some:
     "v < length xs
        \<Longrightarrow> (map_of (zip [0..<length xs] xs) v) = Some (xs ! v)"
  by (induction xs rule: rev_induct) (auto simp add: nth_append map_add_Some_iff)

lemma in_set_zip_lengthE:
  "(x,y) \<in> set(zip [0..<length xs] xs) \<Longrightarrow> (\<lbrakk> x < length xs; xs ! x =y \<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
  by (induction xs rule: rev_induct) (auto simp add: nth_append map_add_Some_iff)

context abs_ast_prob
begin

lemma is_valid_vars_2:
  shows "list_all (\<lambda>v. abs_range_map v \<noteq> None) abs_ast_variable_section"
  by (auto simp add: abs_range_map_def abs_ast_variable_section_def list.pred_set)
end

context ast_problem
begin

definition abs_ast_initial_state
  :: "nat_sas_plus_state" 
  where "abs_ast_initial_state \<equiv> map_of (zip [0..<length astI] astI)"

end

context abs_ast_prob
begin

lemma valid_abs_init_1: "abs_ast_initial_state v \<noteq> None \<longleftrightarrow> v \<in> set abs_ast_variable_section"
  by (simp add: abs_ast_variable_section_def numVars_def wf_initial(1) abs_ast_initial_state_def)

lemma abs_range_map_Some:
  shows "v \<in> set abs_ast_variable_section \<Longrightarrow>
            (abs_range_map v) = Some [0..<length (snd (snd (astDom ! v)))]"
  by (simp add: numVars_def abs_range_map_def o_def abs_ast_variable_section_def map_of_zip_map_Some)

lemma in_abs_v_sec_length: "v \<in> set abs_ast_variable_section \<longleftrightarrow> v < length astDom"
  by (simp add: abs_ast_variable_section_def)

lemma [simp]: "v < length astDom \<Longrightarrow> (abs_ast_initial_state v) = Some (astI ! v)"
  using wf_initial(1)[simplified numVars_def, symmetric]
  by (auto simp add: map_of_zip_Some abs_ast_initial_state_def split: prod.splits)

lemma [simp]: "v < length astDom \<Longrightarrow> astI ! v < length (snd (snd (astDom ! v)))"
  using wf_initial(1)[simplified numVars_def, symmetric] wf_initial
  by (auto simp add: numVals_def abs_ast_initial_state_def
              split: prod.splits)

lemma [intro!]: "v \<in> set abs_ast_variable_section \<Longrightarrow> x < length (snd (snd (astDom ! v))) \<Longrightarrow>
                 x \<in> set (the (abs_range_map v))"
  using abs_range_map_Some
  by (auto simp add: )

lemma [intro!]: "x<length astDom \<Longrightarrow> astI ! x < length (snd (snd (astDom ! x)))"
  using wf_initial[unfolded numVars_def numVals_def]
  by auto

lemma [simp]: "abs_ast_initial_state v = Some a \<Longrightarrow> a < length (snd (snd (astDom ! v)))"
  by(auto simp add: abs_ast_initial_state_def
                    wf_initial(1)[unfolded numVars_def numVals_def, symmetric]
          elim!: in_set_zip_lengthE)

lemma valid_abs_init_2:
  "abs_ast_initial_state v \<noteq> None \<Longrightarrow> (the (abs_ast_initial_state v)) \<in> set (the (abs_range_map v))"
  using valid_abs_init_1
  by auto

end

context ast_problem
begin

definition abs_ast_goal
  :: "nat_sas_plus_state" 
  where "abs_ast_goal \<equiv> map_of astG"

end

context abs_ast_prob
begin

lemma [simp]: "wf_partial_state s \<Longrightarrow> (v, a) \<in> set s \<Longrightarrow> v \<in> set abs_ast_variable_section"
  by (auto simp add: wf_partial_state_def abs_ast_variable_section_def numVars_def
           split: prod.splits)

lemma valid_abs_goal_1: "abs_ast_goal v \<noteq> None \<Longrightarrow> v \<in> set abs_ast_variable_section"
  using wf_goal
  by (auto simp add: abs_ast_goal_def dest!: map_of_SomeD)

lemma in_abs_rangeI: "wf_partial_state s \<Longrightarrow> (v, a) \<in> set s \<Longrightarrow> (a \<in> set (the (abs_range_map v)))"
  by (auto simp add: abs_range_map_Some wf_partial_state_def numVals_def split: prod.splits)

lemma valid_abs_goal_2:
  "abs_ast_goal v \<noteq> None \<Longrightarrow> (the (abs_ast_goal v)) \<in> set (the (abs_range_map v))"
  using wf_goal 
  by (auto simp add: map_of_SomeD weak_map_of_SomeI abs_ast_goal_def intro!: in_abs_rangeI)

end

context ast_problem
begin

definition abs_ast_operator
  :: "ast_operator \<Rightarrow> nat_sas_plus_operator"
  where "abs_ast_operator \<equiv> \<lambda>(name, preconditions, effects, cost). 
       \<lparr> precondition_of = preconditions, 
         effect_of = [(v, x). (_, v, _, x) \<leftarrow> effects] \<rparr>"

end

context abs_ast_prob
begin

lemma abs_rangeI: "wf_partial_state s \<Longrightarrow> (v, a) \<in> set s \<Longrightarrow> (abs_range_map v \<noteq> None)"
  by (auto simp add: wf_partial_state_def abs_range_map_def abs_ast_variable_section_def list.pred_set
                     numVars_def
           split: prod.splits)

lemma abs_valid_operator_1[intro!]:
  "wf_operator op \<Longrightarrow> list_all (\<lambda>(v, a). ListMem v abs_ast_variable_section)
   (precondition_of (abs_ast_operator op))"
  by (cases op; auto simp add: abs_ast_operator_def wf_operator_def list.pred_set ListMem_iff)

lemma wf_operator_preD: "wf_operator (name, pres, effs, cost) \<Longrightarrow> wf_partial_state pres"
  by (simp add: wf_operator_def)

lemma abs_valid_operator_2[intro!]:
  "wf_operator op \<Longrightarrow> 
    list_all (\<lambda>(v, a). (\<exists>y. abs_range_map v = Some y) \<and> ListMem a (the (abs_range_map v)))
             (precondition_of (abs_ast_operator op))"
  by(cases op, 
     auto dest!: wf_operator_preD simp: list.pred_set ListMem_iff abs_ast_operator_def
          intro!: abs_rangeI[simplified not_None_eq] in_abs_rangeI)

lemma wf_operator_effE: "wf_operator (name, pres, effs, cost) \<Longrightarrow>
          (\<lbrakk>distinct (map (\<lambda>(_, v, _, _). v) effs);
            \<And>epres x vp v. (epres,x,vp,v)\<in>set effs \<Longrightarrow> wf_partial_state epres; 
            \<And>epres x vp v.(epres,x,vp,v)\<in>set effs \<Longrightarrow> x < numVars;
            \<And>epres x vp v. (epres,x,vp,v)\<in>set effs \<Longrightarrow> v < numVals x;
            \<And>epres x vp v. (epres,x,vp,v)\<in>set effs \<Longrightarrow> 
                    case vp of None \<Rightarrow> True | Some v \<Rightarrow> v<numVals x\<rbrakk>
             \<Longrightarrow> P)
           \<Longrightarrow> P"
  unfolding wf_operator_def
  by (auto split: prod.splits)
  
lemma abs_valid_operator_3':
  "wf_operator (name, pre, eff, cost) \<Longrightarrow>
     list_all (\<lambda>(v, a). ListMem v abs_ast_variable_section) (map (\<lambda>(_, v, _, a). (v, a)) eff)"
  by (fastforce simp add: list.pred_set ListMem_iff abs_ast_variable_section_def image_def numVars_def
                elim!: wf_operator_effE split: prod.splits)

lemma abs_valid_operator_3[intro!]:
  "wf_operator op \<Longrightarrow>
     list_all (\<lambda>(v, a). ListMem v abs_ast_variable_section) (effect_of (abs_ast_operator op))"
  by (cases op, simp add: abs_ast_operator_def abs_valid_operator_3')

lemma wf_abs_eff: "wf_operator (name, pre, eff, cost) \<Longrightarrow> wf_partial_state (map (\<lambda>(_, v, _, a). (v, a)) eff)"
  by (elim wf_operator_effE, induction eff)
     (fastforce simp: wf_partial_state_def image_def o_def split: prod.split_asm)+
  
lemma abs_valid_operator_4':
  "wf_operator (name, pre, eff, cost) \<Longrightarrow>
     list_all (\<lambda>(v, a). (abs_range_map v \<noteq> None) \<and> ListMem a (the (abs_range_map v))) (map (\<lambda>(_, v, _, a). (v, a)) eff)"
  apply(subst list.pred_set ListMem_iff)+
  apply(drule wf_abs_eff)
  by (metis (mono_tags, lifting) abs_rangeI case_prodI2 in_abs_rangeI)

lemma abs_valid_operator_4[intro!]:
  "wf_operator op \<Longrightarrow>
     list_all (\<lambda>(v, a). (\<exists>y. abs_range_map v = Some y) \<and> ListMem a (the (abs_range_map v)))
              (effect_of (abs_ast_operator op))"
  using abs_valid_operator_4'
  by (cases op, simp add: abs_ast_operator_def)

lemma consistent_list_set: "wf_partial_state s \<Longrightarrow>
   list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') s) s"
  by (auto simp add: list.pred_set wf_partial_state_def eq_key_imp_eq_value split: prod.splits)

lemma abs_valid_operator_5':
  "wf_operator (name, pre, eff, cost) \<Longrightarrow>
     list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') pre) pre"
  apply(drule wf_operator_preD)
  by (intro consistent_list_set)

lemma abs_valid_operator_5[intro!]:
  "wf_operator op \<Longrightarrow>
     list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') (precondition_of (abs_ast_operator op)))
              (precondition_of (abs_ast_operator op))"
  using abs_valid_operator_5'
  by (cases op, simp add: abs_ast_operator_def)

lemma consistent_list_set_2: "distinct (map fst s) \<Longrightarrow>
   list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') s) s"
  by (auto simp add: list.pred_set wf_partial_state_def eq_key_imp_eq_value split: prod.splits)

lemma abs_valid_operator_6':
  assumes "wf_operator (name, pre, eff, cost)"
  shows "list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') (map (\<lambda>(_, v, _, a). (v, a)) eff))
              (map (\<lambda>(_, v, _, a). (v, a)) eff)"
proof-
  have *: "map fst (map (\<lambda>(_, v, _, a). (v, a)) eff) = (map (\<lambda>(_, v,_,_). v) eff)"
    by (induction eff) auto
  show ?thesis
    using assms
    apply(elim wf_operator_effE)
    apply(intro consistent_list_set_2)
    by (subst *)
qed

lemma abs_valid_operator_6[intro!]:
  "wf_operator op \<Longrightarrow> 
     list_all (\<lambda>(v, a). list_all (\<lambda>(v', a'). v \<noteq> v' \<or> a = a') (effect_of (abs_ast_operator op)))
              (effect_of (abs_ast_operator op))"
  using abs_valid_operator_6'
  by (cases op, simp add: abs_ast_operator_def)

end

context ast_problem
begin

definition abs_ast_operator_section
  :: "nat_sas_plus_operator list" 
  where "abs_ast_operator_section \<equiv> [abs_ast_operator op. op \<leftarrow> ast\<delta>]" 

definition abs_prob :: "nat_sas_plus_problem"
  where "abs_prob = \<lparr> 
    variables_of = abs_ast_variable_section,
    operators_of = abs_ast_operator_section,
    initial_of = abs_ast_initial_state,
    goal_of = abs_ast_goal,
    range_of = abs_range_map
  \<rparr>" 

end

context abs_ast_prob
begin

lemma [simp]: "op \<in> set ast\<delta> \<Longrightarrow> (is_valid_operator_sas_plus abs_prob) (abs_ast_operator op)"
  apply(cases op)
  apply(subst is_valid_operator_sas_plus_def Let_def)+
  using wf_operators(2)
  by(fastforce simp add: abs_prob_def)+

lemma abs_ast_operator_section_valid: 
   "list_all (is_valid_operator_sas_plus abs_prob) abs_ast_operator_section"
  by (auto simp: abs_ast_operator_section_def list.pred_set)

lemma abs_prob_valid: "is_valid_problem_sas_plus abs_prob"
  using valid_abs_goal_1 valid_abs_goal_2 valid_abs_init_1 is_valid_vars_2
        abs_ast_operator_section_valid[unfolded abs_prob_def]
  by (auto simp add: is_valid_problem_sas_plus_def Let_def ListMem_iff abs_prob_def)

definition abs_ast_plan 
  :: " SASP_Semantics.plan \<Rightarrow> nat_sas_plus_plan"
  where "abs_ast_plan \<pi>s 
    \<equiv> map (abs_ast_operator o the o lookup_operator) \<pi>s" 

lemma std_then_implici_effs[simp]: "is_standard_operator' (name, pres, effs, layer) \<Longrightarrow> implicit_pres effs = []"
  apply(induction effs)
  by (auto simp add: is_standard_operator'_def implicit_pres_def is_standard_effect'_def)

lemma [simp]: "enabled \<pi> s \<Longrightarrow> lookup_operator \<pi> = Some (name, pres, effs, layer) \<Longrightarrow>
       is_standard_operator' (name, pres, effs, layer) \<Longrightarrow>
       (filter (eff_enabled s) effs) = effs"
  by(auto simp add: enabled_def is_standard_operator'_def eff_enabled_def is_standard_effect'_def filter_id_conv list.pred_set)
  
lemma effs_eq_abs_effs: "(effect_of (abs_ast_operator (name, pres, effs, layer))) = 
                           (map (\<lambda>(_,x,_,v). (x,v)) effs)"
  by (auto simp add: abs_ast_operator_def
           split: option.splits prod.splits)

lemma exect_eq_abs_execute:
      "\<lbrakk>enabled \<pi> s; lookup_operator \<pi> = Some (name, preconds, effs, layer);
        is_standard_operator'(name, preconds, effs, layer)\<rbrakk> \<Longrightarrow>
       execute \<pi> s = (execute_operator_sas_plus s ((abs_ast_operator o the o lookup_operator) \<pi>))"
  using effs_eq_abs_effs
  by (auto simp add: execute_def execute_operator_sas_plus_def)

lemma enabled_then_sas_applicable:
  "enabled \<pi> s \<Longrightarrow> SAS_Plus_Representation.is_operator_applicable_in s ((abs_ast_operator o the o lookup_operator) \<pi>)"
  by (auto simp add: subsuming_states_def enabled_def lookup_operator_def
                     SAS_Plus_Representation.is_operator_applicable_in_def abs_ast_operator_def                     
           split: option.splits prod.splits)

lemma path_to_then_exec_serial: "\<forall>\<pi>\<in>set \<pi>s. lookup_operator \<pi> \<noteq> None \<Longrightarrow>
        path_to s \<pi>s s' \<Longrightarrow>
        s' \<subseteq>\<^sub>m execute_serial_plan_sas_plus s (abs_ast_plan \<pi>s)"
proof(induction \<pi>s arbitrary: s s')
  case (Cons a \<pi>s)
  then show ?case
    by (force simp: exect_eq_abs_execute abs_ast_plan_def lookup_Some_in\<delta> no_cond_effs
              dest: enabled_then_sas_applicable)
qed (auto simp: execute_serial_plan_sas_plus_def abs_ast_plan_def)

lemma map_of_eq_None_iff:
  "(None = map_of xys x) = (x \<notin> fst ` (set xys))"
by (induct xys) simp_all

lemma [simp]: "I = abs_ast_initial_state"
  apply(intro HOL.ext)
  by (auto simp: map_of_eq_None_iff set_map[symmetric] I_def abs_ast_initial_state_def map_of_zip_Some
           dest: map_of_SomeD)

lemma [simp]: "\<forall>\<pi> \<in> set \<pi>s. lookup_operator \<pi> \<noteq> None \<Longrightarrow>
          op\<in>set (abs_ast_plan \<pi>s) \<Longrightarrow> op \<in> set abs_ast_operator_section"
  by (induction \<pi>s) (auto simp: abs_ast_plan_def abs_ast_operator_section_def lookup_Some_in\<delta>)

end

context ast_problem
begin

lemma path_to_then_lookup_Some: "(\<exists>s'\<in>G. path_to s \<pi>s s') \<Longrightarrow> (\<forall>\<pi> \<in> set \<pi>s. lookup_operator \<pi> \<noteq> None)"
  by (induction \<pi>s arbitrary: s) (force simp add: enabled_def split: option.splits)+

lemma valid_plan_then_lookup_Some: "valid_plan \<pi>s \<Longrightarrow> (\<forall>\<pi> \<in> set \<pi>s. lookup_operator \<pi> \<noteq> None)"
  using path_to_then_lookup_Some
  by(simp add: valid_plan_def)

end

context abs_ast_prob
begin

theorem valid_plan_then_is_serial_sol:
  assumes "valid_plan \<pi>s"
  shows "is_serial_solution_for_problem abs_prob (abs_ast_plan \<pi>s)"
  using valid_plan_then_lookup_Some[OF assms] assms
  by (auto simp add: is_serial_solution_for_problem_def valid_plan_def initial_of_def
                       abs_prob_def abs_ast_goal_def G_def subsuming_states_def list_all_iff
                       ListMem_iff map_le_trans path_to_then_exec_serial
           simp del: sas_plus_problem.select_defs)

end

subsection \<open>Translating SAS+ represnetation to Fast-Downward's\<close>

context ast_problem
begin

definition lookup_action:: "nat_sas_plus_operator \<Rightarrow> ast_operator option" where
 "lookup_action op \<equiv>
    find (\<lambda>(_, pres, effs, _). precondition_of op = pres \<and>
                               map (\<lambda>(v,a). ([], v, None, a)) (effect_of op) = effs)
         ast\<delta>"

end

context abs_ast_prob
begin

lemma find_Some: "find P xs = Some x \<Longrightarrow> x \<in> set xs \<and> P x"
  by (auto simp add: find_Some_iff)

lemma distinct_find: "distinct (map f xs) \<Longrightarrow> x \<in> set xs \<Longrightarrow> find (\<lambda>x'. f x' = f x) xs = Some x"
  by (induction xs) (auto simp: image_def)

lemma lookup_operator_find: "lookup_operator nme = find (\<lambda>op. fst op = nme) ast\<delta>"
  by (auto simp: lookup_operator_def intro!: arg_cong[where f = "(\<lambda>x. find x ast\<delta>)"])

lemma lookup_operator_works_1: "lookup_action op = Some \<pi>' \<Longrightarrow> lookup_operator (fst \<pi>') = Some \<pi>'"
  by (auto simp: wf_operators(1) lookup_operator_find lookup_action_def dest: find_Some intro: distinct_find)

lemma lookup_operator_works_2: 
  "lookup_action (abs_ast_operator (name, pres, effs, layer)) = Some (name', pres', effs', layer')
   \<Longrightarrow> pres = pres'"
  by (auto simp: lookup_action_def abs_ast_operator_def dest!: find_Some)

lemma [simp]: "is_standard_operator' (name, pres, effs, layer) \<Longrightarrow>
       map (\<lambda>(v,a). ([], v, None, a)) (effect_of (abs_ast_operator (name, pres, effs, layer))) = effs"
  by (induction effs) (auto simp: is_standard_operator'_def  abs_ast_operator_def is_standard_effect'_def)

lemma lookup_operator_works_3:
  "is_standard_operator' (name, pres, effs, layer) \<Longrightarrow> (name, pres, effs, layer) \<in> set ast\<delta> \<Longrightarrow>
   lookup_action (abs_ast_operator (name, pres, effs, layer)) = Some (name', pres', effs', layer')
   \<Longrightarrow> effs = effs'"
  by(auto simp: is_standard_operator'_def lookup_action_def dest!: find_Some)

lemma mem_find_Some: "x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> \<exists>x'. find P xs = Some x'"
  by (induction xs) auto

lemma [simp]: "precondition_of (abs_ast_operator (x1, a, aa, b)) = a"
  by(simp add: abs_ast_operator_def)

lemma std_lookup_action: "is_standard_operator' ast_op \<Longrightarrow> ast_op \<in> set ast\<delta> \<Longrightarrow> 
                          \<exists>ast_op'. lookup_action (abs_ast_operator ast_op) = Some ast_op'"
  unfolding lookup_action_def
  apply(intro mem_find_Some)
  by (auto split: prod.splits simp: o_def)

lemma is_applicable_then_enabled_1:
      "ast_op \<in> set ast\<delta> \<Longrightarrow>
       \<exists>ast_op'. lookup_operator ((fst o the o lookup_action o abs_ast_operator) ast_op) = Some ast_op'"
  using lookup_operator_works_1 std_lookup_action no_cond_effs
  by auto

lemma lookup_action_Some_in_\<delta>: "lookup_action op = Some ast_op \<Longrightarrow> ast_op \<in> set ast\<delta>"
  using lookup_operator_works_1 lookup_Some_in\<delta> by fastforce

lemma lookup_operator_eq_name: "lookup_operator name = Some (name', pres, effs, layer) \<Longrightarrow> name = name'"
  using lookup_operator_wf(2)
  by fastforce

lemma eq_name_eq_pres: "(name, pres, effs, layer) \<in> set ast\<delta> \<Longrightarrow> (name, pres', effs', layer') \<in> set ast\<delta>
  \<Longrightarrow> pres = pres'"
  using  eq_key_imp_eq_value[OF wf_operators(1)]
  by auto

lemma eq_name_eq_effs: 
  "name = name' \<Longrightarrow> (name, pres, effs, layer) \<in> set ast\<delta> \<Longrightarrow> (name', pres', effs', layer') \<in> set ast\<delta>
  \<Longrightarrow> effs = effs'"
  using eq_key_imp_eq_value[OF wf_operators(1)]
  by auto

lemma is_applicable_then_subsumes:
      "s \<in> valid_states \<Longrightarrow> 
       SAS_Plus_Representation.is_operator_applicable_in s (abs_ast_operator (name, pres, effs, layer)) \<Longrightarrow>
       s \<in> subsuming_states (map_of pres)"
  by (simp add: subsuming_states_def SAS_Plus_Representation.is_operator_applicable_in_def
                  abs_ast_operator_def)

lemma eq_name_eq_pres':
  "\<lbrakk>s \<in> valid_states ; is_standard_operator' (name, pres, effs, layer); (name, pres, effs, layer) \<in> set ast\<delta> ;
    lookup_operator ((fst o the o lookup_action o abs_ast_operator) (name, pres, effs, layer)) = Some (name', pres', effs', layer')\<rbrakk>
    \<Longrightarrow> pres = pres'"
  using lookup_operator_eq_name lookup_operator_works_2      
  by (fastforce dest!: std_lookup_action
                simp: eq_name_eq_pres[OF lookup_action_Some_in_\<delta> lookup_Some_in\<delta>])

lemma is_applicable_then_enabled_2:
  "\<lbrakk>s \<in> valid_states ; ast_op \<in> set ast\<delta> ;
    SAS_Plus_Representation.is_operator_applicable_in s (abs_ast_operator ast_op);
    lookup_operator ((fst o the o lookup_action o abs_ast_operator) ast_op) = Some (name, pres, effs, layer)\<rbrakk>
    \<Longrightarrow> s\<in>subsuming_states (map_of pres)"
  apply(cases ast_op)
  using eq_name_eq_pres' is_applicable_then_subsumes no_cond_effs
  by fastforce
  
lemma is_applicable_then_enabled_3:
  "\<lbrakk>s \<in> valid_states;
    lookup_operator ((fst o the o lookup_action o abs_ast_operator) ast_op) = Some (name, pres, effs, layer)\<rbrakk>
   \<Longrightarrow> s\<in>subsuming_states (map_of (implicit_pres effs))"
  apply(cases ast_op)
  using no_cond_effs
  by (auto dest!: std_then_implici_effs std_lookup_action lookup_Some_in\<delta>
           simp: subsuming_states_def)

lemma is_applicable_then_enabled:
 "\<lbrakk>s \<in> valid_states; ast_op \<in> set ast\<delta>;
   SAS_Plus_Representation.is_operator_applicable_in s (abs_ast_operator ast_op)\<rbrakk>
   \<Longrightarrow> enabled ((fst o the o lookup_action o abs_ast_operator) ast_op) s"
  using is_applicable_then_enabled_1 is_applicable_then_enabled_2 is_applicable_then_enabled_3
  by(simp add: enabled_def split: option.splits)

lemma eq_name_eq_effs':
  assumes "lookup_operator ((fst o the o lookup_action o abs_ast_operator) (name, pres, effs, layer)) =
             Some (name', pres', effs', layer')"
          "is_standard_operator' (name, pres, effs, layer)" "(name, pres, effs, layer) \<in> set ast\<delta>"
          "s \<in> valid_states"
  shows "effs = effs'"
  using std_lookup_action[OF assms(2,3)] assms
  by (auto simp: lookup_operator_works_3[OF assms(2,3)] 
                 eq_name_eq_effs[OF lookup_operator_eq_name lookup_action_Some_in_\<delta> lookup_Some_in\<delta>])

lemma std_eff_enabled'[simp]:
  "is_standard_operator' (name, pres, effs, layer) \<Longrightarrow> s \<in> valid_states \<Longrightarrow> (filter (eff_enabled s) effs) = effs"
  by (induction effs) (auto simp: is_standard_operator'_def is_standard_effect'_def eff_enabled_def subsuming_states_def)

lemma execute_abs:
  "\<lbrakk>s \<in> valid_states; ast_op \<in> set ast\<delta>;
    SAS_Plus_Representation.is_operator_applicable_in s (abs_ast_operator ast_op)\<rbrakk> \<Longrightarrow>
    execute ((fst o the o lookup_action o abs_ast_operator) ast_op) s =
      execute_operator_sas_plus s (abs_ast_operator ast_op)"
  using no_cond_effs
  by(cases ast_op)
    (fastforce simp add: execute_def execute_operator_sas_plus_def effs_eq_abs_effs
               dest: is_applicable_then_enabled_1 eq_name_eq_effs'[unfolded o_def]
               split: option.splits)+

fun sat_preconds_as where
  "sat_preconds_as s [] = True"
| "sat_preconds_as s (op#ops) = 
     (SAS_Plus_Representation.is_operator_applicable_in s op \<and>
      sat_preconds_as (execute_operator_sas_plus s op) ops)"

lemma exec_serial_then_path_to':
  "\<lbrakk>s \<in> valid_states;
   \<forall>op\<in>set ops. \<exists>ast_op\<in> set ast\<delta>. op = abs_ast_operator ast_op;
   (sat_preconds_as s ops)\<rbrakk> \<Longrightarrow>
   path_to s (map (fst o the o lookup_action) ops) (execute_serial_plan_sas_plus s ops)"
proof(induction ops arbitrary: s)
  case (Cons a ops)
  then show ?case
    using execute_abs is_applicable_then_enabled execute_preserves_valid
    apply simp
    by metis
qed auto

end

fun rem_condless_ops where
  "rem_condless_ops s [] = []"
| "rem_condless_ops s (op#ops) = 
     (if SAS_Plus_Representation.is_operator_applicable_in s op then
      op # (rem_condless_ops (execute_operator_sas_plus s op) ops)
      else [])"

context abs_ast_prob
begin

lemma exec_rem_consdless: "execute_serial_plan_sas_plus s (rem_condless_ops s ops) = execute_serial_plan_sas_plus s ops"
  by (induction ops arbitrary: s) auto

lemma rem_conless_sat: "sat_preconds_as s (rem_condless_ops s ops)"
  by (induction ops arbitrary: s) auto

lemma set_rem_condlessD: "x \<in> set (rem_condless_ops s ops) \<Longrightarrow> x \<in> set ops"
  by (induction ops arbitrary: s) auto

lemma exec_serial_then_path_to:
  "\<lbrakk>s \<in> valid_states;
   \<forall>op\<in>set ops. \<exists>ast_op\<in> set ast\<delta>. op = abs_ast_operator ast_op\<rbrakk> \<Longrightarrow>
   path_to s (((map (fst o the o lookup_action)) o rem_condless_ops s) ops)
             (execute_serial_plan_sas_plus s ops)"
  using  rem_conless_sat
  by (fastforce dest!: set_rem_condlessD
                intro!: exec_serial_then_path_to'
                          [where s = s and ops = "rem_condless_ops s ops",
                           unfolded exec_rem_consdless])

lemma is_serial_solution_then_abstracted:
  "is_serial_solution_for_problem abs_prob ops
   \<Longrightarrow> \<forall>op\<in>set ops. \<exists>ast_op\<in> set ast\<delta>. op = abs_ast_operator ast_op"
  by(auto simp: is_serial_solution_for_problem_def abs_prob_def Let_def list.pred_set
                    ListMem_iff abs_ast_operator_section_def
          split: if_splits)

lemma lookup_operator_works_1': "lookup_action op = Some \<pi>' \<Longrightarrow> \<exists>op. lookup_operator (fst \<pi>') = op"
  using lookup_operator_works_1 by auto

lemma is_serial_sol_then_valid_plan_1:
 "\<lbrakk>is_serial_solution_for_problem abs_prob ops;
   \<pi> \<in> set ((map (fst o the o lookup_action) o rem_condless_ops I) ops)\<rbrakk> \<Longrightarrow>
  lookup_operator \<pi> \<noteq> None"
  using std_lookup_action lookup_operator_works_1 no_cond_effs
  by (fastforce dest!: set_rem_condlessD is_serial_solution_then_abstracted
                simp: valid_plan_def list.pred_set ListMem_iff)

lemma is_serial_sol_then_valid_plan_2:
 "\<lbrakk>is_serial_solution_for_problem abs_prob ops\<rbrakk> \<Longrightarrow>
   (\<exists>s'\<in>G. path_to I ((map (fst o the o lookup_action) o rem_condless_ops I) ops) s')"
  using I_valid
  by (fastforce intro: path_to_pres_valid exec_serial_then_path_to
                intro!: bexI[where x = "execute_serial_plan_sas_plus I ops"]
                dest: is_serial_solution_then_abstracted
                simp: list.pred_set ListMem_iff abs_ast_operator_section_def
                      G_def subsuming_states_def is_serial_solution_for_problem_def
                      abs_prob_def abs_ast_goal_def)+

end

context ast_problem
begin

definition "decode_abs_plan \<equiv> (map (fst o the o lookup_action) o rem_condless_ops I)"

end

context abs_ast_prob
begin

theorem is_serial_sol_then_valid_plan:
  "\<lbrakk>is_serial_solution_for_problem abs_prob ops\<rbrakk> \<Longrightarrow>
   valid_plan (decode_abs_plan ops)"
  using is_serial_sol_then_valid_plan_1 is_serial_sol_then_valid_plan_2
  by(simp add: valid_plan_def decode_abs_plan_def)

end

end