theory Fmap
imports Map_Extra Fset
begin

text {* Ideally, this should only require a linear order on the domain type
        but for the sake of convenience I've got both requiring it as the
        the ordering of the graph list is just the pairwise linear order. *}
definition fmaps :: "('a \<rightharpoonup> 'b) set" 
where "fmaps = Collect (finite \<circ> dom)"

typedef (open) ('a, 'b) fmap = "fmaps :: ('a \<rightharpoonup> 'b) set" 
  by (rule_tac x="empty" in exI, simp add:fmaps_def)

notation Rep_fmap ("\<langle>_\<rangle>\<^sub>m")

declare Rep_fmap [simp]
declare Rep_fmap_inverse [simp]
declare Abs_fmap_inverse [simp]

lemma Rep_fmap_intro [intro!]:
  "Rep_fmap x = Rep_fmap y \<Longrightarrow> x = y"
  by (simp add:Rep_fmap_inject)

lemma Rep_fmap_elim [elim]:
  "\<lbrakk> x = y; Rep_fmap x = Rep_fmap y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

lemma Abs_fmap_inv [simp]:  "finite (dom f) \<Longrightarrow> Rep_fmap (Abs_fmap f) = f"
  apply (subgoal_tac "f \<in> fmaps")
  apply (metis Abs_fmap_inverse)
  apply (simp_all add: fmaps_def)
done

lemma Abs_fmap_inj [intro]: 
  "\<lbrakk> Abs_fmap f = Abs_fmap g; finite (dom f); finite (dom g) \<rbrakk> \<Longrightarrow> f = g"
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

setup_lifting type_definition_fmap

lift_definition fdom :: "('a, 'b) fmap \<Rightarrow> 'a fset" is dom
  by (simp add:fmaps_def fsets_def)

lift_definition fran :: "('a, 'b) fmap \<Rightarrow> 'b fset" is ran
  by (simp add:fmaps_def fsets_def)

lift_definition fmempty :: "('a, 'b) fmap" is "Map.empty"
  by (simp add:fmaps_def)

lemma fdom_empty [simp]: 
  "fdom f = \<lbrace>\<rbrace> \<Longrightarrow> f = fmempty"
  by (auto simp add:fdom.rep_eq fmempty.rep_eq)

lemma fran_empty [simp]: 
  "fran f = \<lbrace>\<rbrace> \<Longrightarrow> f = fmempty"
  apply (auto elim!:Rep_fset_elim simp add:fran.rep_eq fmempty.rep_eq fempty.rep_eq)
  apply (metis empty_iff option.exhaust ranI)
done

definition "fmap_list f = map (\<lambda> x. (x, the (Rep_fmap f x))) (flist (fdom f))"
lift_definition list_fmap :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) fmap" is "map_of"
  by (simp add:fmaps_def finite_dom_map_of)

lemma fmap_list_inv[simp]: 
  "list_fmap (fmap_list f) = f"
  apply (auto simp add:list_fmap.rep_eq fmap_list_def)
  apply (metis fdom.rep_eq flist_inv fset_rep_eq map_of_map_keys)
done

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

lemma fdom_fmap_list [simp]: "fdom (list_fmap xs) = fset (map fst xs)"
  by (auto simp add:fdom.rep_eq list_fmap.rep_eq dom_map_of_conv_image_fst)

lemma list_fmap_inv[simp]:
  "\<lbrakk>distinct (map fst xs); sorted (map fst xs)\<rbrakk> \<Longrightarrow> fmap_list (list_fmap xs) = xs"
  by (auto intro!:map_idI simp add:list_fmap.rep_eq fmap_list_def map_graph_list finite_dom_graph Rep_fmap_inverse finite_dom_map_of)

lemma map_fst_fmap_list [simp]:
  "map fst (fmap_list f) = flist (fdom f)"
  by (auto intro!:map_idI simp add:flist_def fmap_list_def)

lemma fmap_list_props [simp]:
  "sorted (map fst (fmap_list f))"
  "distinct (map fst (fmap_list f))"
  by (simp_all)

lemma fmap_list_props2 [simp]:
  "distinct (fmap_list f)"
  by (metis (lifting) distinct_zipI1 fmap_list_props(2) zip_map_fst_snd)

lemma fdom_list: "fdom f = Abs_fset (fst ` set (fmap_list f))"
  apply (auto simp add:fdom_def fmap_list_def dom_map_graph)
  apply (metis (lifting) fst_conv image_iff)+
done

lemma fran_list: "fran f = Abs_fset (snd ` set (fmap_list f))"
  apply (auto simp add:fran.rep_eq fdom.rep_eq fmap_list_def image_def)
  apply (auto simp add:ran_def)
done

lemma fmext[intro]: "(\<And> x. \<langle>f\<rangle>\<^sub>m x = \<langle>g\<rangle>\<^sub>m x) \<Longrightarrow> f = g"
  by (auto)

lemma fdomI: "\<langle>m\<rangle>\<^sub>m a = Some b ==> a \<in>\<^sub>f fdom m"
  by (auto simp add:fdom_def fmember.rep_eq)

lemma fdomD: "a \<in>\<^sub>f fdom m \<Longrightarrow> \<exists>b. \<langle>m\<rangle>\<^sub>m a = Some b"
  by (auto simp add:fdom_def fmember.rep_eq)

lemma fdomIff [iff, simp del]: "(a \<in>\<^sub>f fdom m) = (\<langle>m\<rangle>\<^sub>m a ~= None)"
  by (auto simp add:fdom_def fmember.rep_eq)

default_sort type

(*
instantiation fmap :: (type,type) discrete_cpo
begin

definition below_fmap_def:
  "(x::('a, 'b) fmap) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_fmap_def)

end
*)

end