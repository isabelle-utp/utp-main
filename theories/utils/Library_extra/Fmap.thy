theory Fmap
imports HOLCF Map_Extra Fset
begin

default_sort linorder

text {* Ideally, this should only require a linear order on the domain type
        but for the sake of convenience I've got both requiring it as the
        the ordering of the graph list is just the pairwise linear order. *}
definition fmaps :: "('a \<rightharpoonup> 'b) set" 
where "fmaps = Collect (finite \<circ> dom)"

typedef (open) ('a, 'b) fmap = "fmaps :: ('a \<rightharpoonup> 'b) set" 
  by (rule_tac x="empty" in exI, simp add:fmaps_def)

lemma Abs_fmap_inv [simp]:  "finite (dom f) \<Longrightarrow> Rep_fmap (Abs_fmap f) = f"
  apply (subgoal_tac "f \<in> fmaps")
  apply (metis Abs_fmap_inverse)
  apply (simp_all add: fmaps_def)
done

lemma Abs_fmap_inj [intro]: "\<lbrakk> Abs_fmap f = Abs_fmap g; finite (dom f); finite (dom g) \<rbrakk> \<Longrightarrow> f = g"
  by (metis Abs_fmap_inv)

lemma fin_dom_fmap [simp]: "finite (dom (Rep_fmap f))"
  apply (insert Rep_fmap[of f])
  apply (simp add:fmaps_def)
done

lemma fin_ran_fmap [simp]: "finite (ran (Rep_fmap f))"
  apply (insert Rep_fmap[of f])
  apply (simp add:fmaps_def)
done

lemma fin_map_graph_fmap [simp]: "finite (map_graph (Rep_fmap f))"
  by (metis fin_dom_fmap finite_dom_graph)
  
definition "fmap_list f = sorted_list_of_set (map_graph (Rep_fmap f))"
definition "list_fmap xs = Abs_fmap (map_of xs)"

lemma fmap_list_inv[simp]: 
  "list_fmap (fmap_list f) = f"
  by (simp add:list_fmap_def fmap_list_def map_graph_list finite_dom_graph Rep_fmap_inverse)

lemma map_graph_set: "\<lbrakk>distinct (map fst xs); sorted xs\<rbrakk> \<Longrightarrow> set xs = map_graph (map_of xs)"
  apply (induct xs)
  apply (simp add:map_graph_def)
  apply (simp)
  apply (subgoal_tac "sorted xs")
  apply (simp)
  apply (simp add:map_graph_def)
  apply (auto)
  apply (force)
  apply (metis (lifting) map_of_is_SomeD option.inject snd_conv)
  apply (metis (lifting) drop_1_Cons sorted_drop)
done

lemma list_fmap_inv[simp]:
  "\<lbrakk>distinct (map fst xs); sorted xs\<rbrakk> \<Longrightarrow> fmap_list (list_fmap xs) = xs"
  apply (simp add:list_fmap_def fmap_list_def map_graph_list finite_dom_graph Rep_fmap_inverse finite_dom_map_of)
  apply (simp add:map_graph_set[THEN sym])
  apply (metis (lifting) distinct_map finite_set sorted_distinct_set_unique sorted_list_of_set)
done

lemma fmap_list_props [simp]:
  "sorted (fmap_list xs)"
  "distinct (fmap_list xs)"
  "distinct (map fst (fmap_list xs))"
  apply (simp_all add:fmap_list_def fin_dom_fmap finite_dom_graph sorted_list_of_set)
  apply (metis distinct_map fin_map_graph_fmap functional_def map_graph_functional sorted_list_of_set)
done

setup_lifting type_definition_fmap

lift_definition fdom :: "('a, 'b) fmap \<Rightarrow> 'a fset" is dom
  by (simp add:fmaps_def fsets_def)

lift_definition fran :: "('a, 'b) fmap \<Rightarrow> 'b fset" is ran
  by (simp add:fmaps_def fsets_def)

lemma fdom_fmap_list: "fdom f = Abs_fset (fst ` set (fmap_list f))"
  by (simp add:fdom_def fmap_list_def dom_map_graph)

lemma fran_fmap_list: "fran f = Abs_fset (snd ` set (fmap_list f))"
  apply (simp add:fran_def fmap_list_def)
  apply (metis fin_dom_fmap finite_dom_graph ran_map_graph sorted_list_of_set)
done

lift_definition fmempty :: "('a, 'b) fmap" is "Map.empty"
  by (simp add:fmaps_def)

lift_definition fmlookup :: "'a \<Rightarrow> ('a, 'b) fmap \<Rightarrow> 'b option" is "\<lambda> x f. f x"
  by simp

lemma fmext[intro]: "(\<And> x. fmlookup x f = fmlookup x g) \<Longrightarrow> f = g"
  apply (auto simp add:fmlookup_def)
  apply (drule ext)
  apply (metis Rep_fmap_inject)
done

lemma fdomI: "fmlookup a m = Some b ==> a \<in>\<^sub>f fdom m"
  by (auto simp add:fdom_def fmember.rep_eq fmlookup.rep_eq)

lemma fdomD: "a \<in>\<^sub>f fdom m \<Longrightarrow> \<exists>b. fmlookup a m = Some b"
  by (auto simp add:fdom_def fmember.rep_eq fmlookup.rep_eq)

lemma fdomIff [iff, simp del]: "(a \<in>\<^sub>f fdom m) = (fmlookup a m ~= None)"
  by (auto simp add:fdom_def fmember.rep_eq fmlookup.rep_eq)

default_sort type

instantiation fmap :: (type,type) discrete_cpo
begin

definition below_fmap_def:
  "(x::('a, 'b) fmap) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_fmap_def)

end

end