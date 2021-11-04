section \<open>Executable PDDL Checker\<close>
theory PDDL_STRIPS_Checker
imports
  PDDL_STRIPS_Semantics

  Error_Monad_Add
  "HOL.String"

  (*"HOL-Library.Code_Char"     TODO: This might lead to performance loss! CHECK! *)
  "HOL-Library.Code_Target_Nat"

  "HOL-Library.While_Combinator"

  "Containers.Containers"
begin

subsection \<open>Generic DFS Reachability Checker\<close>
text \<open>Used for subtype checks\<close>

definition "E_of_succ succ \<equiv> { (u,v). v\<in>set (succ u) }"
lemma succ_as_E: "set (succ x) = E_of_succ succ `` {x}"
  unfolding E_of_succ_def by auto

context
  fixes succ :: "'a \<Rightarrow> 'a list"
begin

  private abbreviation (input) "E \<equiv> E_of_succ succ"


definition "dfs_reachable D w \<equiv>
  let (V,w,brk) = while (\<lambda>(V,w,brk). \<not>brk \<and> w\<noteq>[]) (\<lambda>(V,w,_).
    case w of v#w \<Rightarrow>
    if D v then (V,v#w,True)
    else if v\<in>V then (V,w,False)
    else
      let V = insert v V in
      let w = succ v @ w in
      (V,w,False)
    ) ({},w,False)
  in brk"


context
  fixes w\<^sub>0 :: "'a list"
  assumes finite_dfs_reachable[simp, intro!]: "finite (E\<^sup>* `` set w\<^sub>0)"
begin

  private abbreviation (input) "W\<^sub>0 \<equiv> set w\<^sub>0"

definition "dfs_reachable_invar D V W brk \<longleftrightarrow>
    W\<^sub>0 \<subseteq> W \<union> V
  \<and> W \<union> V \<subseteq> E\<^sup>* `` W\<^sub>0
  \<and> E``V \<subseteq> W \<union> V
  \<and> Collect D \<inter> V = {}
  \<and> (brk \<longrightarrow> Collect D \<inter> E\<^sup>* `` W\<^sub>0 \<noteq> {})"

lemma card_decreases: "
   \<lbrakk>finite V; y \<notin> V; dfs_reachable_invar D V (Set.insert y W) brk \<rbrakk>
   \<Longrightarrow> card (E\<^sup>* `` W\<^sub>0 - Set.insert y V) < card (E\<^sup>* `` W\<^sub>0 - V)"
  apply (rule psubset_card_mono)
  apply (auto simp: dfs_reachable_invar_def)
  done

lemma all_neq_Cons_is_Nil[simp]: (* Odd term remaining in goal \<dots> *)
  "(\<forall>y ys. x2 \<noteq> y # ys) \<longleftrightarrow> x2 = []" by (cases x2) auto

lemma dfs_reachable_correct: "dfs_reachable D w\<^sub>0 \<longleftrightarrow> Collect D \<inter> E\<^sup>* `` set w\<^sub>0 \<noteq> {}"
  unfolding dfs_reachable_def
  apply (rule while_rule[where
    P="\<lambda>(V,w,brk). dfs_reachable_invar D V (set w) brk \<and> finite V"
    and r="measure (\<lambda>V. card (E\<^sup>* `` (set w\<^sub>0) - V)) <*lex*> measure length <*lex*> measure (\<lambda>True\<Rightarrow>0 | False\<Rightarrow>1)"
    ])
  subgoal by (auto simp: dfs_reachable_invar_def)
  subgoal
    apply (auto simp: neq_Nil_conv succ_as_E[of succ] split: if_splits)
    by (auto simp: dfs_reachable_invar_def Image_iff intro: rtrancl.rtrancl_into_rtrancl)
  subgoal by (fastforce simp: dfs_reachable_invar_def dest: Image_closed_trancl)
  subgoal by blast
  subgoal by (auto simp: neq_Nil_conv card_decreases)
  done

end

definition "tab_succ l \<equiv> Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l Mapping.empty)"


lemma Some_eq_map_option [iff]: "(Some y = map_option f xo) = (\<exists>z. xo = Some z \<and> f z = y)"
  by (auto simp add: map_option_case split: option.split)


lemma tab_succ_correct: "E_of_succ (tab_succ l) = set l"
proof -
  have "set (Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l m) u) = set l `` {u} \<union> set (Mapping.lookup_default [] m u)"
    for m u
    apply (induction l arbitrary: m)
    by (auto
      simp: Mapping.lookup_default_def Mapping.map_default_def Mapping.default_def
      simp: lookup_map_entry' lookup_update' keys_is_none_rep Option.is_none_def
      split: if_splits
    )
  from this[where m=Mapping.empty] show ?thesis
    by (auto simp: E_of_succ_def tab_succ_def lookup_default_empty)
qed

end

lemma finite_imp_finite_dfs_reachable:
  "\<lbrakk>finite E; finite S\<rbrakk> \<Longrightarrow> finite (E\<^sup>*``S)"
  apply (rule finite_subset[where B="S \<union> (Relation.Domain E \<union> Relation.Range E)"])
  apply (auto simp: intro: finite_Domain finite_Range elim: rtranclE)
  done

lemma dfs_reachable_tab_succ_correct: "dfs_reachable (tab_succ l) D vs\<^sub>0 \<longleftrightarrow> Collect D \<inter> (set l)\<^sup>*``set vs\<^sub>0 \<noteq> {}"
  apply (subst dfs_reachable_correct)
  by (simp_all add: tab_succ_correct finite_imp_finite_dfs_reachable)



subsection \<open>Implementation Refinements\<close>

subsubsection \<open>Of-Type\<close>

definition "of_type_impl G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))"


fun ty_term' where
  "ty_term' varT objT (term.VAR v) = varT v"
| "ty_term' varT objT (term.CONST c) = Mapping.lookup objT c"

lemma ty_term'_correct_aux: "ty_term' varT objT t = ty_term varT (Mapping.lookup objT) t"
  by (cases t) auto

lemma ty_term'_correct[simp]: "ty_term' varT objT = ty_term varT (Mapping.lookup objT)"
  using ty_term'_correct_aux by auto

context ast_domain begin

  definition "of_type1 pt T \<longleftrightarrow> pt \<in> subtype_rel\<^sup>* `` set (primitives T)"

  lemma of_type_refine1: "of_type oT T \<longleftrightarrow> (\<forall>pt\<in>set (primitives oT). of_type1 pt T)"
    unfolding of_type_def of_type1_def by auto

  definition "STG \<equiv> (tab_succ (map subtype_edge (types D)))"

  lemma subtype_rel_impl: "subtype_rel = E_of_succ (tab_succ (map subtype_edge (types D)))"
    by (simp add: tab_succ_correct subtype_rel_def)

  lemma of_type1_impl: "of_type1 pt T \<longleftrightarrow> dfs_reachable (tab_succ (map subtype_edge (types D))) ((=)pt) (primitives T)"
    by (simp add: subtype_rel_impl of_type1_def dfs_reachable_tab_succ_correct tab_succ_correct)

  lemma of_type_impl_correct: "of_type_impl STG oT T \<longleftrightarrow> of_type oT T"
    unfolding of_type1_impl STG_def of_type_impl_def of_type_refine1 ..

  definition mp_constT :: "(object, type) mapping" where
    "mp_constT = Mapping.of_alist (consts D)"

  lemma mp_objT_correct[simp]: "Mapping.lookup mp_constT = constT"
    unfolding mp_constT_def constT_def
    by transfer (simp add: Map_To_Mapping.map_apply_def)






  text \<open>Lifting the subtype-graph through wf-checker\<close>
  context
    fixes ty_ent :: "'ent \<rightharpoonup> type"  \<comment> \<open>Entity's type, None if invalid\<close>
  begin

    definition "is_of_type' stg v T \<longleftrightarrow> (
      case ty_ent v of
        Some vT \<Rightarrow> of_type_impl stg vT T
      | None \<Rightarrow> False)"

    lemma is_of_type'_correct: "is_of_type' STG v T = is_of_type ty_ent v T"
      unfolding is_of_type'_def is_of_type_def of_type_impl_correct ..

    fun wf_pred_atom' where "wf_pred_atom' stg (p,vs) \<longleftrightarrow> (case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 (is_of_type' stg) vs Ts)"

    lemma wf_pred_atom'_correct: "wf_pred_atom' STG pvs = wf_pred_atom ty_ent pvs"
      by (cases pvs) (auto simp: is_of_type'_correct[abs_def] split:option.split)

    fun wf_atom' :: "_ \<Rightarrow> 'ent atom \<Rightarrow> bool" where
      "wf_atom' stg (atom.predAtm p vs) \<longleftrightarrow> wf_pred_atom' stg (p,vs)"
    | "wf_atom' stg (atom.Eq a b) = (ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None)"

    lemma wf_atom'_correct: "wf_atom' STG a = wf_atom ty_ent a"
      by (cases a) (auto simp: wf_pred_atom'_correct is_of_type'_correct[abs_def] split: option.splits)

    fun wf_fmla' :: "_ \<Rightarrow> ('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla' stg (Atom a) \<longleftrightarrow> wf_atom' stg a"
    | "wf_fmla' stg \<bottom> \<longleftrightarrow> True"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla' stg \<phi>"

    lemma wf_fmla'_correct: "wf_fmla' STG \<phi> \<longleftrightarrow> wf_fmla ty_ent \<phi>"
      by (induction \<phi> rule: wf_fmla.induct) (auto simp: wf_atom'_correct)

    fun wf_fmla_atom1' where
      "wf_fmla_atom1' stg (Atom (predAtm p vs)) \<longleftrightarrow> wf_pred_atom' stg (p,vs)"
    | "wf_fmla_atom1' stg _ \<longleftrightarrow> False"

    lemma wf_fmla_atom1'_correct: "wf_fmla_atom1' STG \<phi> = wf_fmla_atom ty_ent \<phi>"
      by (cases \<phi> rule: wf_fmla_atom.cases) (auto
        simp: wf_atom'_correct is_of_type'_correct[abs_def] split: option.splits)

    fun wf_effect' where
      "wf_effect' stg (Effect a d) \<longleftrightarrow>
          (\<forall>ae\<in>set a. wf_fmla_atom1' stg ae)
        \<and> (\<forall>de\<in>set d.  wf_fmla_atom1' stg de)"

    lemma wf_effect'_correct: "wf_effect' STG e = wf_effect ty_ent e"
      by (cases e) (auto simp: wf_fmla_atom1'_correct)

  end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>

  fun wf_action_schema' :: "_ \<Rightarrow> _ \<Rightarrow> ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema' stg conT (Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyv = ty_term' (map_of params) conT
      in
        distinct (map fst params)
      \<and> wf_fmla' tyv stg pre
      \<and> wf_effect' tyv stg eff)"

  lemma wf_action_schema'_correct: "wf_action_schema' STG mp_constT s = wf_action_schema s"
    by (cases s) (auto simp: wf_fmla'_correct wf_effect'_correct)

  definition wf_domain' :: "_ \<Rightarrow> _ \<Rightarrow> bool" where
    "wf_domain' stg conT \<equiv>
      wf_types
    \<and> distinct (map (predicate_decl.pred) (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
    \<and> distinct (map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (consts D). wf_type T)
    \<and> distinct (map ast_action_schema.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema' stg conT a)
    "

  lemma wf_domain'_correct: "wf_domain' STG mp_constT = wf_domain"
    unfolding wf_domain_def wf_domain'_def
    by (auto simp: wf_action_schema'_correct)


end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Application of Effects\<close>

context ast_domain begin
  text \<open>We implement the application of an effect by explicit iteration over
    the additions and deletions\<close>
  fun apply_effect_exec
    :: "object ast_effect \<Rightarrow> world_model \<Rightarrow> world_model"
  where
    "apply_effect_exec (Effect a d) s
      = fold (\<lambda>add s. Set.insert add s) a
          (fold (\<lambda>del s. Set.remove del s) d s)"

  lemma apply_effect_exec_refine[simp]:
    "apply_effect_exec (Effect (a) (d)) s
    = apply_effect (Effect (a) (d)) s"
  proof(induction a arbitrary: s)
    case Nil
    then show ?case
    proof(induction d arbitrary: s)
      case Nil
      then show ?case by auto
    next
      case (Cons a d)
      then show ?case
        by (auto simp add: image_def)
    qed
  next
    case (Cons a a)
    then show ?case
    proof(induction d arbitrary: s)
      case Nil
      then show ?case by (auto; metis Set.insert_def sup_assoc insert_iff)
    next
      case (Cons a d)
      then show ?case
        by (auto simp: Un_commute minus_set_fold union_set_fold)
    qed
  qed

  lemmas apply_effect_eq_impl_eq
    = apply_effect_exec_refine[symmetric, unfolded apply_effect_exec.simps]

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Well-Formedness\<close>

context ast_problem begin

  text \<open> We start by defining a mapping from objects to types. The container
    framework will generate efficient, red-black tree based code for that
    later. \<close>

  type_synonym objT = "(object, type) mapping"

  definition mp_objT :: "(object, type) mapping" where
    "mp_objT = Mapping.of_alist (consts D @ objects P)"

  lemma mp_objT_correct[simp]: "Mapping.lookup mp_objT = objT"
    unfolding mp_objT_def objT_alt
    by transfer (simp add: Map_To_Mapping.map_apply_def)

  text \<open>We refine the typecheck to use the mapping\<close>

  definition "is_obj_of_type_impl stg mp n T = (
    case Mapping.lookup mp n of None \<Rightarrow> False | Some oT \<Rightarrow> of_type_impl stg oT T
  )"

  lemma is_obj_of_type_impl_correct[simp]:
    "is_obj_of_type_impl STG mp_objT = is_obj_of_type"
    apply (intro ext)
    apply (auto simp: is_obj_of_type_impl_def is_obj_of_type_def of_type_impl_correct split: option.split)
    done

  text \<open>We refine the well-formedness checks to use the mapping\<close>

  definition wf_fact' :: "objT \<Rightarrow> _ \<Rightarrow> fact \<Rightarrow> bool"
    where
    "wf_fact' ot stg \<equiv> wf_pred_atom' (Mapping.lookup ot) stg"

  lemma wf_fact'_correct[simp]: "wf_fact' mp_objT STG = wf_fact"
    by (auto simp: wf_fact'_def wf_fact_def wf_pred_atom'_correct[abs_def])


  definition "wf_fmla_atom2' mp stg f
    = (case f of formula.Atom (predAtm p vs) \<Rightarrow> (wf_fact' mp stg (p,vs)) | _ \<Rightarrow> False)"

  lemma wf_fmla_atom2'_correct[simp]:
    "wf_fmla_atom2' mp_objT STG \<phi> = wf_fmla_atom objT \<phi>"
    apply (cases \<phi> rule: wf_fmla_atom.cases)
    by (auto simp: wf_fmla_atom2'_def wf_fact_def split: option.splits)

  definition "wf_problem' stg conT mp \<equiv>
      wf_domain' stg conT
    \<and> distinct (map fst (objects P) @ map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> (\<forall>f\<in>set (init P). wf_fmla_atom2' mp stg f)
    \<and> wf_fmla' (Mapping.lookup mp) stg (goal P)"

  lemma wf_problem'_correct:
    "wf_problem' STG mp_constT mp_objT = wf_problem"
    unfolding wf_problem_def wf_problem'_def wf_world_model_def
    by (auto simp: wf_domain'_correct wf_fmla'_correct)


  text \<open>Instantiating actions will yield well-founded effects.
    Corollary of @{thm wf_instantiate_action_schema}.\<close>
  lemma wf_effect_inst_weak:
    fixes a args
    defines "ai \<equiv> instantiate_action_schema a args"
    assumes A: "action_params_match a args"
      "wf_action_schema a"
    shows "wf_effect_inst (effect ai)"
    using wf_instantiate_action_schema[OF A] unfolding ai_def[symmetric]
    by (cases ai) (auto simp: wf_effect_inst_alt)


end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>


context wf_ast_domain begin
  text \<open>Resolving an action yields a well-founded action schema.\<close>
  (* TODO: This must be implicitly proved when showing that plan execution
    preserves wf. Try to remove this redundancy!*)
  lemma resolve_action_wf:
    assumes "resolve_action_schema n = Some a"
    shows "wf_action_schema a"
  proof -
    from wf_domain have
      X1: "distinct (map ast_action_schema.name (actions D))"
      and X2: "\<forall>a\<in>set (actions D). wf_action_schema a"
      unfolding wf_domain_def by auto

    show ?thesis
      using assms unfolding resolve_action_schema_def
      by (auto simp add: index_by_eq_Some_eq[OF X1] X2)
  qed

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


subsubsection \<open>Execution of Plan Actions\<close>

text \<open>We will perform two refinement steps, to summarize redundant operations\<close>

text \<open>We first lift action schema lookup into the error monad. \<close>
context ast_domain begin
  definition "resolve_action_schemaE n \<equiv>
    lift_opt
      (resolve_action_schema n)
      (ERR (shows ''No such action schema '' o shows n))"
end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

end \<comment> \<open>Theory\<close>
