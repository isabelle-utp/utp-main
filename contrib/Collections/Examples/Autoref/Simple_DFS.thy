header {* \isaheader{Simple DFS Algorithm} *}
theory Simple_DFS
imports 
  "../../Refine_Dflt" 
begin


text {*
  This example presents the usage of the recursion combinator
  @{text "RECT"}. The usage of the partial correct version 
  @{text "REC"} is similar.

  We define a simple DFS-algorithm, prove a simple correctness
  property, and do data refinement to an efficient implementation.
*}

subsection {* Definition *}
(* TODO: Warning, this is not exactly DFS, as V is not updated in FOREACH.
  Replace by more accurate example from ICFContainers paper draft! *)
text {* Recursive DFS-Algorithm. 
  @{text "E"} is the edge relation of the graph, @{text "vd"} the node to 
  search for, and @{text "v0"} the start node.
  Already explored nodes are 
  stored in @{text "V"}.*}
definition dfs :: "('a \<Rightarrow>'a set) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool nres" 
  where
  "dfs succ vd v0 \<equiv> REC\<^sub>T (\<lambda>D (V,v). 
    if v=vd then RETURN True 
    else if v\<in>V then RETURN False
    else do {
      let V=insert v V;
      FOREACH\<^sub>C (succ v) (op = False) (\<lambda>v' _. D (V,v')) False }
  ) ({},v0)"

subsection {* Correctness *}

text {* As simple correctness property, we show:
  If the algorithm returns true, then @{text "vd"} is reachable from 
  @{text "v0"}.
*}
lemma dfs_sound:
  fixes succ
  defines "E \<equiv> {(v,v'). v'\<in>succ v}"
  assumes F: "finite {v. (v0,v)\<in>E\<^sup>*}"
  shows "dfs succ vd v0 \<le> SPEC (\<lambda>r. r \<longrightarrow> (v0,vd)\<in>E\<^sup>*)"
proof -
  have S: "\<And>v. succ v = E``{v}"
    by (auto simp: E_def)
  
  from F show ?thesis
    unfolding dfs_def S
    apply (refine_rcg refine_vcg impI
      RECT_rule[where 
        \<Phi>="\<lambda>(V,v). (v0,v)\<in>E\<^sup>* \<and> V\<subseteq>{v. (v0,v)\<in>E\<^sup>*}" and
        V="finite_psupset ({v. (v0,v)\<in>E\<^sup>*}) <*lex*> {}"]
      FOREACHc_rule[where I="\<lambda>_ r. r \<longrightarrow> (v0, vd) \<in> E\<^sup>*"]
    )
    apply (auto intro: finite_subset[of _ "{v'. (v0,v')\<in>E\<^sup>*}"])
    apply rprems
    apply (auto simp: finite_psupset_def)
    done    
qed

subsection {* Data Refinement and Determinization *}
text {*
  Next, we use automatic data refinement and transfer to generate an
  executable algorithm. The edges function
  is refined to a successor function returning a list-set.
*}
schematic_lemma dfs_impl_refine_aux:
  fixes succi and succ :: "nat \<Rightarrow> nat set" and vd v0 :: nat
  assumes [autoref_rules]: "(succi,succ)\<in>Id\<rightarrow>\<langle>Id\<rangle>list_set_rel"
  notes [autoref_rules] = IdI[of v0] IdI[of vd]
  shows "(?f::?'c, dfs succ vd v0)\<in>?R"
  unfolding dfs_def[abs_def]
  apply (autoref_monadic)
  done

text {* We can configure our tool to use different implementations.
  Here, we use lists for sets of natural numbers. *}
schematic_lemma dfs_impl_refine_aux2:
  fixes succi and succ :: "nat \<Rightarrow> nat set" and vd v0 :: nat
  assumes [autoref_rules]: "(succi,succ)\<in>Id\<rightarrow>\<langle>Id\<rangle>dflt_rs_rel" 
  notes [autoref_rules] = IdI[of v0] IdI[of vd]
  notes [autoref_tyrel] = ty_REL[where 'a="nat set" and R="\<langle>Id\<rangle>list_set_rel"]
  shows "(?f::?'c, dfs succ vd v0)\<in>?R"
  unfolding dfs_def[abs_def]
  apply (autoref_monadic)
  done

text {* We can also leave the type of the nodes and its implementation
  unspecified. However, the implementation relation must be single-valued,
  and we need a comparison operator on nodes *}

(*schematic_lemma 
  fixes vs vd :: 'a and Rv :: "('c\<times>'a) set"
  assumes [autoref_rules]: "(vsi,vs)\<in>Rv" "(vdi,vd)\<in>Rv" 
  shows "(?f::?'c, vs = vd)\<in>?R"
  apply (autoref (keep_goal) phases: id_op rel_inf fix_rel)
*)


schematic_lemma dfs_impl_refine_aux3:
  fixes succi and succ :: "'a::linorder \<Rightarrow> 'a set" 
    and Rv :: "('ai\<times>'a) set"
  assumes [relator_props]: "single_valued Rv"
  assumes [autoref_rules_raw]: "(cmpk, dflt_cmp op \<le> op <)\<in>(Rv\<rightarrow>Rv\<rightarrow>Id)"
  notes [autoref_tyrel] = ty_REL[where 'a="'a set" and R="\<langle>Rv\<rangle>dflt_rs_rel"]
  assumes P_REF[autoref_rules]: 
    "(succi,succ)\<in>Rv\<rightarrow>\<langle>Rv\<rangle>list_set_rel"
    "(vdi,vd::'a)\<in>Rv"
    "(v0i,v0)\<in>Rv"
  shows "(?f::?'c, dfs succ vd v0)\<in>?R"
  unfolding dfs_def[abs_def]
  by autoref_monadic

text {* Next, we extract constants from the refinement lemmas,
  and prepare them for code-generation *}
concrete_definition dfs_impl for succi vd ?v0.0 uses dfs_impl_refine_aux
prepare_code_thms dfs_impl_def
concrete_definition dfs_impl2 for succi vd ?v0.0 uses dfs_impl_refine_aux2
prepare_code_thms dfs_impl2_def
concrete_definition dfs_impl3 for succi vd ?v0.0 uses dfs_impl_refine_aux3
prepare_code_thms dfs_impl3_def

text {* Finally, we export code using the code-generator *}
export_code dfs_impl dfs_impl2 dfs_impl3 in SML
export_code dfs_impl dfs_impl2 dfs_impl3 in OCaml
export_code dfs_impl dfs_impl2 dfs_impl3 in Haskell
export_code dfs_impl dfs_impl2 dfs_impl3 in Scala

text {* Derived correctness lemma for the generated function *}
lemma dfs_impl_correct:
  fixes succi succ
  defines "E \<equiv> {(s, s'). s' \<in> succ s}"
  assumes S: "(succi,succ) \<in> Id \<rightarrow> \<langle>Id\<rangle>list_set_rel"
  assumes F: "finite (E\<^sup>*``{v0})"
  assumes R: "dfs_impl succi vd v0"
  shows "(v0,vd)\<in>E\<^sup>*"
proof -
  note dfs_impl.refine[OF S, of vd v0, THEN nres_relD]
  also
  have F': "finite {v. (v0, v) \<in> {(v, v'). v' \<in> succ v}\<^sup>*}" 
    using F 
    apply (fo_rule back_subst, assumption)
    by (auto simp: E_def)
  note dfs_sound[OF F']
  finally show ?thesis using R 
    by (auto simp: E_def)

qed

end
