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

end