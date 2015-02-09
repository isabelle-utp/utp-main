(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: bmap.thy                                                             *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

theory bmap
imports bset "Library_extra/Map_Extra"
begin

lemma bset_image_empty [simp]:
  "bset_image f {}\<^sub>b = {}\<^sub>b"
  by (transfer, simp)
  
lift_definition bfunctional :: "('a * 'b) bset \<Rightarrow> bool" is functional .

lemma bfunctional_empty [intro]:
  "bfunctional {}\<^sub>b"
  by (transfer, metis empty_iff functional_def inj_on_def)

lemma functional_map_prod: "\<lbrakk> functional(R); inj(f) \<rbrakk> \<Longrightarrow> functional (map_prod f g ` R)"
  by (auto simp add:functional_def inj_on_def)

lemma bfunctional_map_prod: "\<lbrakk> bfunctional(R); inj f \<rbrakk> \<Longrightarrow> bfunctional (bset_image (map_prod f g) R)"
  by (transfer, auto intro: functional_map_prod)
  
subsection {* Type Definition *}

definition bmap :: "('a \<rightharpoonup> 'b) set" where
"bmap \<equiv> {f :: ('a \<rightharpoonup> 'b). dom(f) \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t}"

theorem bmap_member (* [iff] *) :
"f \<in> bmap \<longleftrightarrow> dom(f) \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t"
  by (simp add: bmap_def)
  
typedef ('a, 'b) bmap = "bmap :: ('a \<rightharpoonup> 'b) set"
morphisms DestBMap MkBMap
apply (rule_tac x = "Map.empty" in exI)
apply (simp add: bmap_def)
apply (unfold leq_card_def)
apply (simp only: inj_on_empty image_empty empty_subsetI)
apply (simp)
done

setup_lifting type_definition_bmap

lift_definition bmempty :: "('a, 'b) bmap" is empty
  by (auto simp add:bmap_def)

term fun_upd
  
lift_definition bmap_upd :: "('a, 'b) bmap \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) bmap" is 
"\<lambda> m k v. fun_upd m k (Some v)"
  by (metis bmap_def bset_member dom_fun_upd insert_bset mem_Collect_eq option.distinct(2))
  
lift_definition bmap_comp :: "('b, 'c) bmap \<Rightarrow> ('a, 'b) bmap \<Rightarrow> ('a, 'c) bmap" is map_comp
  apply (auto simp add: bmap_def)
  apply (metis leq_card_subset leq_card_trans map_comp_dom)
done

lift_definition bmap_add :: "('a, 'b) bmap \<Rightarrow> ('a, 'b) bmap => ('a, 'b) bmap" is map_add
  apply (auto simp add: bmap_def)
  apply (metis infinite_bset_limit union_ordLeq_infinite)
done

lift_definition bmap_dom_res :: "('a, 'b) bmap \<Rightarrow> 'a bset \<Rightarrow> ('a, 'b) bmap" is restrict_map
  by (metis bmap_def bset_def dom_restrict inter1_bset mem_Collect_eq)

lift_definition bmap_ran_res :: "('a, 'b) bmap \<Rightarrow> 'b bset \<Rightarrow> ('a, 'b) bmap" is ran_restrict_map
  apply (simp add:bset_def bmap_def)
  apply (metis dom_ran_restrict leq_card_subset leq_card_trans)
done

lift_definition bmap_dom_res_by :: "('a::type, 'b::type) bmap \<Rightarrow> 'a bset \<Rightarrow> ('a, 'b) bmap" 
is "\<lambda> m A. restrict_map m (- A)"
  apply (auto simp add: bmap_def bset_def)
  apply (metis Diff_Compl bset_member minus_bset)
done

lift_definition bmap_ran_res_by :: "('a::type, 'b::type) bmap \<Rightarrow> 'b bset \<Rightarrow> ('a, 'b) bmap" 
is "\<lambda> m A. ran_restrict_map m (- A)"
  apply (auto simp add: bmap_def bset_def)
  apply (metis dom_ran_restrict leq_card_subset leq_card_trans)
done

lift_definition bmdom :: "('a, 'b) bmap \<Rightarrow> 'a bset" is dom
  by (auto simp add:bmap_def)
    
lemma ran_dom_card: "ran(f) \<preceq>\<^sub>c dom(f)"
  apply (unfold leq_card_iff_ordLeq)
  apply (rule card_of_ordLeqI[of "the \<circ> map_inv f"])
  apply (rule inj_onI)
  apply (auto simp add:map_inv_def ran_def)
  apply (metis (mono_tags) option.sel someI)
  apply (metis (mono_tags) someI)
done
  
lift_definition bmran :: "('a, 'b) bmap \<Rightarrow> 'b bset" is ran
  apply (simp add:bmap_def bset_def)
  apply (metis leq_card_trans ran_dom_card)
done

lemma map_graph_dom_card: 
  "map_graph(f) \<preceq>\<^sub>c dom(f)"
  apply (simp add: leq_card_def)
  apply (rule_tac x="fst" in exI)
  apply (auto)
  apply (metis functional_def map_graph_functional)
  apply (rule_tac x="b" in exI)
  apply (simp add:map_graph_def)
done

lift_definition bmap_graph :: "('a, 'b) bmap \<Rightarrow> ('a * 'b) bset" is map_graph
  apply (auto simp add: bset_def bmap_def)
  apply (metis leq_card_trans map_graph_dom_card)
done

lift_definition bmap_inv :: "('a, 'b) bmap \<Rightarrow> ('b, 'a) bmap" is map_inv
  apply (simp add: bmap_def)
  apply (metis leq_card_trans ran_dom_card)
done

definition bApply :: "('a * 'b) bset \<Rightarrow> 'a \<Rightarrow> 'b option" ("_[_]\<^sub>b" [999,0] 999) where
"bApply R x = (if (\<exists>! x y. (x, y) \<in>\<^sub>b R) then Some (THE y. (x, y) \<in>\<^sub>b R) else None)"

(*
lemma bApply_bmap_graph:
  "bApply (bmap_graph f) x = DestBMap f x"
proof -
  have "(\<exists>!x y. (x, y) \<in> DestBSet (bmap_graph f))"
    apply (transfer)
  apply (simp add: bApply_def)
  sledgehammer
*)
  
lemma map_graph_empty [simp]:
  "map_graph empty = {}"
  by (simp add: map_graph_def)

lemma bmap_graph_bmempty [simp]:
  "bmap_graph bmempty = {}\<^sub>b"
  by (transfer, simp)

lemma bmap_graph_functional: "bfunctional (bmap_graph m)"
  by (transfer, simp)
  
lemma bmap_graph_inj:
  "inj bmap_graph"
  apply (auto simp add:inj_on_def)
  apply (transfer)
  apply (metis map_graph_inv)
done

lemma dom_graph_map_card: 
  "dom (graph_map R) \<preceq>\<^sub>c R"
  apply (auto simp add: leq_card_def)
  apply (rule_tac x="\<lambda> x. (x, the (graph_map R x))" in exI)
  apply (auto)
  apply (rule inj_onI)
  apply (auto simp add:graph_map_def)
  apply (case_tac "x \<in> fst ` R")
  apply (simp_all)
  apply (metis Domain.simps fst_eq_Domain someI)
done
  
lift_definition graph_bmap :: "('a * 'b) bset \<Rightarrow> ('a, 'b) bmap" is graph_map
  apply (simp add:bset_def bmap_def)
  apply (metis dom_graph_map_card leq_card_trans)
done

lemma graph_bmap_empty [simp]: "graph_bmap {}\<^sub>b = bmempty"
  by (transfer, simp)

lemma bmap_graph_inv [simp]: "graph_bmap (bmap_graph m) = m"
  by (transfer, simp)
  
lemma graph_bmap_inv: "bfunctional m \<Longrightarrow> bmap_graph (graph_bmap m) = m"
  by (transfer, simp)

definition bmap_map :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a, 'b) bmap \<Rightarrow> ('c, 'd) bmap" where
"bmap_map f g m = (graph_bmap (bset_image (map_prod f g) (bmap_graph m)))"

lemma bmap_map_id: "bmap_map id id = id"  
  apply (rule ext)
  apply (auto simp add: bmap_map_def)
  apply (metis bmap_graph_inv bset.map_id0 id_apply prod.map_id0)
done

lemma bmap_dist_comp: "bmap_map (g1 \<circ> f1) (g2 \<circ> f2) = bmap_map g1 g2 \<circ> bmap_map f1 f2"
  apply (rule ext)
  apply (simp add: bmap_map_def)
  apply (subst graph_bmap_inv)
  apply (auto simp add: bmap_map_def bfunctional_map_prod bmap_graph_functional bset.map_comp map_prod_compose)
oops
  
definition bmap_fsts :: "('a, 'b) bmap \<Rightarrow> 'a set" where
"bmap_fsts m = fst ` DestBSet (bmap_graph m)" 

definition bmap_snds :: "('a, 'b) bmap \<Rightarrow> 'b set" where
"bmap_snds m = snd ` DestBSet (bmap_graph m)" 

definition
   bmap_rel :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'b) bmap \<Rightarrow> ('c, 'd) bmap \<Rightarrow> bool"
where "bmap_rel f g m n = bset_rel (rel_prod f g) (bmap_graph m) (bmap_graph n)"

text {* Note: as yet we cannot prove that bmap is a BNF. I don't think it is. *}

end
