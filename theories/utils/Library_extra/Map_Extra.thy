theory Map_Extra
imports Main "~~/src/HOL/Library/Char_ord"
begin

definition functional :: "('a * 'b) set \<Rightarrow> bool" where
"functional g = inj_on fst g"

definition functional_list :: "('a * 'b) list \<Rightarrow> bool" where
"functional_list xs = (\<forall> x y z. ListMem (x,y) xs \<and> ListMem (x,z) xs \<longrightarrow> y = z)"

lemma functional_insert [simp]: "functional (insert (x,y) g) \<longleftrightarrow> (g``{x} \<subseteq> {y} \<and> functional g)"
  by (auto simp add:functional_def inj_on_def image_def)

lemma functional_listD: "\<lbrakk>finite g; functional g\<rbrakk> \<Longrightarrow> functional_list (sorted_list_of_set g)"
  by (force simp add:functional_list_def ListMem_iff functional_def inj_on_def)

lemma functional_list_nil[simp]: "functional_list []"
  by (simp add:functional_list_def ListMem_iff)

lemma functional_list: "functional_list xs \<longleftrightarrow> functional (set xs)"
  apply (induct xs)
  apply (simp add:functional_def)
  apply (simp add:functional_def functional_list_def ListMem_iff)
  apply (safe)
  apply (force)
  apply (force)
  apply (force)
  apply (force)
  apply (force)
  apply (force)
  apply (force)
  apply (force)
done

definition map_graph :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a * 'b) set" where
"map_graph f = {(x,y) | x y. f x = Some y}"

definition graph_map :: "('a * 'b) set \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"graph_map g = (\<lambda> x. if (x \<in> fst ` g) then Some (SOME y. (x,y) \<in> g) else None)"

lemma map_graph_functional[simp]: "functional (map_graph f)"
  by (simp add:functional_def map_graph_def inj_on_def)

lemma map_graph_inv [simp]: "graph_map (map_graph f) = f"
  by (auto intro!:ext simp add:map_graph_def graph_map_def image_def)

lemma graph_map_empty[simp]: "graph_map {} = empty"
  by (simp add:graph_map_def)

lemma graph_map_insert [simp]: "\<lbrakk>functional g; g``{x} \<subseteq> {y}\<rbrakk> \<Longrightarrow> graph_map (insert (x,y) g) = (graph_map g)(x \<mapsto> y)"
  by (rule ext, auto simp add:graph_map_def)  

lemma dom_map_graph: "dom f = fst ` (map_graph f)"
  by (simp add: map_graph_def dom_def image_def)

lemma ran_map_graph: "ran f = snd ` (map_graph f)"
  by (simp add: map_graph_def ran_def image_def)

lemma finite_dom_graph: "finite (dom f) \<Longrightarrow> finite (map_graph f)"
  apply (simp add:dom_map_graph)
  apply (drule finite_imageD)
  apply (simp_all add:inj_on_def map_graph_def)
done

lemma finite_dom_ran [simp]: "finite (dom f) \<Longrightarrow> finite (ran f)"
  apply (drule finite_dom_graph)
  apply (simp add:ran_map_graph)
done

lemma graph_map_inv [simp]: "functional g \<Longrightarrow> map_graph (graph_map g) = g"
  apply (auto simp add:map_graph_def graph_map_def functional_def)
  apply (smt DomainE fst_eq_Domain not_Some_eq option.inject tfl_some)
  apply (simp add:inj_on_def)
  apply (metis (lifting) Pair_eq fst_eqD someI)
  apply (metis (lifting) fst_conv image_iff)
done


lemma functional_list_graph: "\<lbrakk>functional_list xs; sorted xs; distinct xs\<rbrakk> \<Longrightarrow> map_of xs = graph_map (set xs)"
  apply (simp add:functional_list)
  apply (induct xs)
  apply (simp)
  apply (auto)
  apply (rule ext)
  apply (auto)
  apply (metis sorted_Cons)
done

lemma map_graph_list: "\<lbrakk>finite g; functional g\<rbrakk> \<Longrightarrow> map_of (sorted_list_of_set g) = graph_map g"
  apply (subgoal_tac "\<exists> xs. functional_list xs \<and> sorted xs \<and> distinct xs \<and> g = set xs")
  apply (auto)
  apply (simp add:sorted_list_of_set_sort_remdups distinct_remdups_id sorted_sort_id functional_list_graph)
  apply (auto dest:functional_listD)
done

definition map_inv :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'a)" where
"map_inv f \<equiv> \<lambda> y. if (y \<in> ran f) then Some (SOME x. f x = Some y) else None"

lemma map_inv_empty [simp]: "map_inv empty = empty"
  by (simp add:map_inv_def)

lemma map_inv_Some [simp]: "map_inv Some = Some"
  by (simp add:map_inv_def ran_def)

lemma map_inv_f_f [simp]: 
  "\<lbrakk> inj_on f (dom f); f x = Some y \<rbrakk> \<Longrightarrow> map_inv f y = Some x"
  apply (auto simp add: map_inv_def)
  apply (rule some_equality)
  apply (auto simp add:inj_on_def dom_def ran_def)
done

lemma dom_map_inv [simp]:
  "dom (map_inv f) = ran f"
  apply (auto simp add:map_inv_def)
  apply (case_tac "x \<in> ran f")
  apply (simp_all)
done

lemma ran_map_inv [simp]:
  "inj_on f (dom f) \<Longrightarrow> ran (map_inv f) = dom f"
  apply (auto simp add:map_inv_def ran_def)
  apply (rule_tac x="a" in exI)
  apply (force intro:someI)
  apply (rule_tac x="y" in exI)
  apply (auto)
  apply (rule some_equality, simp_all)
  apply (auto simp add:inj_on_def dom_def)
done

lemma dom_image_ran: "f ` dom f = Some ` ran f"
  by (auto simp add:dom_def ran_def image_def)

lemma inj_map_inv [intro]:
  "inj_on f (dom f) \<Longrightarrow> inj_on (map_inv f) (ran f)"
  apply (auto simp add:map_inv_def inj_on_def dom_def ran_def)
  apply (frule_tac P="\<lambda> xa. f xa = Some x" in some_equality)
  apply (auto)
  apply (smt option.inject someI)
done

lemma inj_map_bij: "inj_on f (dom f) \<Longrightarrow> bij_betw f (dom f) (Some ` ran f)"
  by (auto simp add:inj_on_def dom_def ran_def image_def bij_betw_def)

lemma dom_left_map_add [simp]: "x \<in> dom g \<Longrightarrow> (f ++ g) x = g x"
  by (auto simp add:map_add_def dom_def)

lemma dom_right_map_add [simp]: "\<lbrakk> x \<notin> dom g; x \<in> dom f \<rbrakk> \<Longrightarrow> (f ++ g) x = f x"
  by (auto simp add:map_add_def dom_def)

lemma map_self_adjoin_complete [intro]: 
  assumes "dom f \<inter> ran f = {}" "inj_on f (dom f)"
  shows "inj_on (map_inv f ++ f) (dom f \<union> ran f)"
  apply (rule inj_onI)
  apply (insert assms)
  apply (case_tac "x \<in> dom f")
  apply (simp)
  apply (case_tac "y \<in> dom f")
  apply (simp add:inj_on_def)
  apply (case_tac "y \<in> ran f")
  apply (subgoal_tac "y \<in> dom (map_inv f)")
  apply (simp)
  apply (metis Int_iff domD empty_iff ranI ran_map_inv)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (case_tac "y \<in> dom f")
  apply (simp)
  apply (case_tac "y \<in> ran f")
  apply (subgoal_tac "y \<in> dom (map_inv f)")
  apply (simp)
  apply (metis Int_iff domD empty_iff ranI ran_map_inv)
  apply (simp)
  apply (metis Int_iff domD empty_iff ranI ran_map_inv)
  apply (simp)
  apply (metis (lifting) inj_map_inv inj_on_contraD)
done

lemma inj_completed_map [intro]:
  "\<lbrakk> dom f = ran f; inj_on f (dom f) \<rbrakk> \<Longrightarrow> inj (Some ++ f)"
  apply (drule inj_map_bij)
  apply (auto simp add:bij_betw_def)
  apply (auto simp add:inj_on_def)[1]
  apply (case_tac "x \<in> dom f")
  apply (simp)
  apply (case_tac "y \<in> dom f")
  apply (simp)
  apply (simp add:ran_def)
  apply (case_tac "y \<in> dom f")
  apply (auto intro:ranI)
done

lemma bij_completed_map [intro]:
  "\<lbrakk> dom f = ran f; inj_on f (dom f) \<rbrakk> \<Longrightarrow> 
   bij_betw (Some ++ f) UNIV (range Some)"
  apply (auto intro: inj_completed_map simp add:bij_betw_def)
  apply (case_tac "xa \<in> dom f")
  apply (simp)
  apply (metis domD rangeI)
  apply (simp)
  apply (simp add:image_def)
  apply (metis (full_types) dom_image_ran dom_left_map_add image_iff map_add_dom_app_simps(3))
done

lemma bij_map_Some:
  "bij_betw f a (Some ` b) \<Longrightarrow> bij_betw (the \<circ> f) a b"
  apply (auto simp add:bij_betw_def)
  apply (smt comp_inj_on f_the_inv_into_f inj_on_def the.simps)
  apply (smt image_iff the.simps)
  apply (metis imageI image_compose the.simps)
done

lemma ran_map_add [simp]: 
  "m`(dom m \<inter> dom n) = n`(dom m \<inter> dom n) \<Longrightarrow> 
   ran(m++n) = ran n \<union> ran m"
  apply (auto simp add:ran_def)
  apply (metis map_add_find_right)
  apply (case_tac "a \<in> dom n")
  apply (subgoal_tac "\<exists> b. n b = Some x")
  apply (auto)
  apply (rule_tac x="b" in exI)
  apply (simp)
  apply (metis (hide_lams, no_types) IntI domI image_iff)
  apply (metis (full_types) map_add_None map_add_dom_app_simps(1) map_add_dom_app_simps(3) not_None_eq)
done

lemma ran_maplets [simp]: 
  "\<lbrakk> length xs = length ys; distinct xs \<rbrakk> \<Longrightarrow> ran [xs [\<mapsto>] ys] = set ys"
    by (induct rule:list_induct2, simp_all)

lemma inj_map_add:
  "\<lbrakk> inj_on f (dom f); inj_on g (dom g); ran f \<inter> ran g = {} \<rbrakk> \<Longrightarrow> 
   inj_on (f ++ g) (dom f \<union> dom g)"
  apply (auto simp add:inj_on_def)
  apply (smt disjoint_iff_not_equal domIff map_add_Some_iff map_add_dom_app_simps(1) ranI)
  apply (metis domI)
  apply (metis disjoint_iff_not_equal ranI)
  apply (metis disjoint_iff_not_equal domIff map_add_Some_iff ranI)
  apply (metis domI)
done


lemma map_inv_add [simp]:
  assumes "inj_on f (dom f)" "inj_on g (dom g)" 
          "dom f \<inter> dom g = {}" "ran f \<inter> ran g = {}" 
  shows "map_inv (f ++ g) = map_inv f ++ map_inv g"
proof (rule ext)

  from assms have minj: "inj_on (f ++ g) (dom (f ++ g))"
    by (simp, metis inj_map_add sup_commute)

  fix x
  have "x \<in> ran g \<Longrightarrow> map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
  proof -
    assume ran:"x \<in> ran g"
    then obtain y where dom:"g y = Some x" "y \<in> dom g"
      by (auto simp add:ran_def)

    hence "(f ++ g) y = Some x"
      by simp

    with assms minj ran dom show "map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
      by simp
  qed

  moreover have "\<lbrakk> x \<notin> ran g; x \<in> ran f \<rbrakk> \<Longrightarrow> map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
  proof -
    assume ran:"x \<notin> ran g" "x \<in> ran f"
    with assms obtain y where dom:"f y = Some x" "y \<in> dom f" "y \<notin> dom g"
      by (auto simp add:ran_def)

    with ran have "(f ++ g) y = Some x"
      by (simp)

    with assms minj ran dom show "map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
      by simp
  qed

  moreover from assms minj have "\<lbrakk> x \<notin> ran g; x \<notin> ran f \<rbrakk> \<Longrightarrow> map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"

    apply (auto simp add:map_inv_def ran_def map_add_def)
    apply (metis dom_left_map_add map_add_def map_add_dom_app_simps(3))

  done

  ultimately show "map_inv (f ++ g) x = (map_inv f ++ map_inv g) x"
    apply (case_tac "x \<in> ran g")
    apply (simp)
    apply (case_tac "x \<in> ran f")
    apply (simp_all)
  done
qed

lemma map_add_lookup [simp]: 
  "x \<notin> dom f \<Longrightarrow> ([x \<mapsto> y] ++ f) x = Some y"
  by (simp add:map_add_def dom_def)
  
lemma distinct_map_dom: 
  "x \<notin> set xs \<Longrightarrow> x \<notin> dom [xs [\<mapsto>] ys]"
  by (simp add:dom_def)

lemma distinct_map_ran:
  "\<lbrakk> distinct xs; y \<notin> set ys; length xs = length ys \<rbrakk> \<Longrightarrow> 
   y \<notin> ran ([xs [\<mapsto>] ys])"
  apply (simp add:map_upds_def)
  apply (subgoal_tac "distinct (map fst (rev (zip xs ys)))")
  apply (simp add:ran_distinct)
  apply (metis (hide_lams, no_types) image_iff set_zip_rightD surjective_pairing)
  apply (simp add:zip_rev[THEN sym])
done

lemma maplets_lookup[rule_format,dest]: 
  "\<lbrakk> length xs = length ys; distinct xs \<rbrakk> \<Longrightarrow> 
     \<forall> y. [xs [\<mapsto>] ys] x = Some y \<longrightarrow> y \<in> set ys"
  by (induct rule:list_induct2, auto)

lemma maplets_distinct_inj [intro]:
  "\<lbrakk> length xs = length ys; distinct xs; distinct ys; set xs \<inter> set ys = {} \<rbrakk> \<Longrightarrow> 
   inj_on [xs [\<mapsto>] ys] (set xs)"
  apply (induct rule:list_induct2)
  apply (simp_all)
  apply (rule conjI)
  apply (rule inj_onI)
  apply (case_tac "xa = x")
  apply (simp)
  apply (case_tac "xa = y")
  apply (simp)
  apply (simp)
  apply (case_tac "ya = x")
  apply (simp)
  apply (simp add:inj_on_def)
  apply (auto)
  apply (case_tac "xa = y")
  apply (simp)
  apply (metis maplets_lookup)
done


lemma map_inv_maplet[simp]: "map_inv [x \<mapsto> y] = [y \<mapsto> x]"
  by (auto simp add:map_inv_def)

lemma map_inv_maplets [simp]:
  "\<lbrakk> length xs = length ys; distinct xs; distinct ys; set xs \<inter> set ys = {} \<rbrakk> \<Longrightarrow> 
  map_inv [xs [\<mapsto>] ys] = [ys [\<mapsto>] xs]"
  apply (induct rule:list_induct2)
  apply (simp_all)
  apply (subgoal_tac "map_inv ([xs [\<mapsto>] ys] ++ [x \<mapsto> y]) = map_inv [xs [\<mapsto>] ys] ++ map_inv [x \<mapsto> y]")
  apply (simp)
  apply (rule map_inv_add)
  apply (auto)
done
  
lemma maplets_lookup_nth [rule_format,simp]:
  "\<lbrakk> length xs = length ys; distinct xs \<rbrakk> \<Longrightarrow> 
   \<forall> i < length ys. [xs [\<mapsto>] ys] (xs ! i) = Some (ys ! i)"
  apply (induct rule:list_induct2)
  apply (auto)
  apply (case_tac i)
  apply (simp_all)
  apply (metis nth_mem)
  apply (case_tac i)
  apply (auto)
done

end