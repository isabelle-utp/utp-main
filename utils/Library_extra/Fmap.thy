theory Fmap
imports Map_Extra FSet_extra
begin

text {* Ideally, this should only require a linear order on the domain type
        but for the sake of convenience I've got both requiring it as the
        the ordering of the graph list is just the pairwise linear order. *}
definition fmaps :: "('a \<rightharpoonup> 'b) set" 
where "fmaps = Collect (finite \<circ> dom)"

typedef ('a, 'b) fmap = "fmaps :: ('a \<rightharpoonup> 'b) set" 
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

lemma Abs_fmap_inj: 
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
setup_lifting type_definition_fset

lift_definition fdom :: "('a, 'b) fmap \<Rightarrow> 'a fset" is dom
  by (simp add:fmaps_def)

lift_definition fran :: "('a, 'b) fmap \<Rightarrow> 'b fset" is ran
  by (simp add:fmaps_def)

instantiation fmap :: (type,type) monoid_add
begin

lift_definition zero_fmap :: "('a, 'b) fmap" is "Map.empty"
  by (simp add:fmaps_def)

lift_definition plus_fmap :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" is map_add
  by (simp add:fmaps_def)

instance
  apply (intro_classes)
  apply (auto simp add:plus_fmap.rep_eq zero_fmap.rep_eq)
done
end

abbreviation fmempty :: "('a, 'b) fmap"
where "fmempty \<equiv> 0"

definition "fmap_list f = map (\<lambda> x. (x, the (\<langle>f\<rangle>\<^sub>m x))) (flist (fdom f))"

lift_definition list_fmap :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) fmap" is "map_of"
  by (simp add:fmaps_def finite_dom_map_of)

lift_definition fmap_graph :: "('a, 'b) fmap \<Rightarrow> ('a * 'b) fset" is "map_graph"
  by (simp add: fmaps_def finite_dom_graph)


lift_definition fmap_upd :: "('a, 'b) fmap \<Rightarrow> 'a \<Rightarrow> 'b option \<Rightarrow> ('a, 'b) fmap" is "fun_upd"
  by (auto simp add:fmaps_def)

lemma fdom_empty [simp]: 
  "fdom f = \<lbrace>\<rbrace> \<Longrightarrow> f = 0"
  by (erule fset_elim, auto simp add:fdom.rep_eq zero_fmap.rep_eq)

lemma fran_empty [simp]: 
  "fran f = \<lbrace>\<rbrace> \<Longrightarrow> f = 0"
  apply (auto elim!:fset_elim simp add:fran.rep_eq zero_fmap.rep_eq)
  apply (metis empty_iff option.exhaust ranI)
done

lemma fdom_fmempty [simp]: "fdom(0) = \<lbrace>\<rbrace>"
  by (auto intro:fmember_intro elim:fmember_elim simp add:fdom.rep_eq zero_fmap.rep_eq)

lemma fdom_plus [simp]: "fdom(x + y) = fdom(x) |\<union>| fdom(y)"
  by (force intro:fmember_intro elim:fmember_elim simp add:fdom.rep_eq plus_fmap.rep_eq)

lemma fmap_list_empty [simp]:
  "fmap_list(0) = []"
  by (simp add:fmap_list_def flist_def fdom.rep_eq zero_fmap.rep_eq)

lemma fmap_list_inv [simp]: 
  "list_fmap (fmap_list f) = f"
  apply (auto simp add:list_fmap.rep_eq fmap_list_def)
  apply (metis fdom.rep_eq flist_inv finset.rep_eq map_of_map_keys)
done

lemma length_fmap_list [simp]: "length (fmap_list x) = fcard (fdom x)"
  apply (simp add: fcard_def fdom.rep_eq fmap_list_def)
  apply (metis distinct_card fdom.rep_eq flist_props(2) flist_set)
done

lemma fmap_list_nth: 
  "i < fcard(fdom(f)) \<Longrightarrow> fmap_list f ! i = (let k = flist (fdom f) ! i in (k, the (\<langle>f\<rangle>\<^sub>m k)))"
  by (simp add: fmap_list_def Let_def fcard_flist)

lemma fdom_fmap_list [simp]: "fdom (list_fmap xs) = finset (map fst xs)"
  by (force intro:fmember_intro elim:fmember_elim simp add:fdom.rep_eq finset.rep_eq list_fmap.rep_eq dom_map_of_conv_image_fst)

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
  apply (simp_all add: fset_inverse image_image)
done

lemma fran_list: "fran f = Abs_fset (snd ` set (fmap_list f))"
  by (metis fmap_list_inv fmap_list_props(2) fran.rep_eq fset_inverse list_fmap.rep_eq ran_distinct)

lemma fmext[intro]: "(\<And> x. \<langle>f\<rangle>\<^sub>m x = \<langle>g\<rangle>\<^sub>m x) \<Longrightarrow> f = g"
  by (auto)

lemma fdomI: "\<langle>m\<rangle>\<^sub>m a = Some b ==> a |\<in>| fdom m"
  by (auto simp add:fdom_def fmember.rep_eq)

lemma fdomD: "a |\<in>| fdom m \<Longrightarrow> \<exists>b. \<langle>m\<rangle>\<^sub>m a = Some b"
  by (auto simp add:fdom_def fmember.rep_eq)

lemma fdomIff [iff, simp del]: "(a |\<in>| fdom m) = (\<langle>m\<rangle>\<^sub>m a ~= None)"
  by (auto simp add:fdom_def fmember.rep_eq)

nonterminal mupdbinds and mupdbind

syntax
  "_mupdbind" :: "['a, 'a] => mupdbind"               ("(2_ :=\<^sub>m/ _)")
  ""          :: "mupdbind => mupdbinds"               ("_")
  "_mupdbinds":: "[mupdbind, mupdbinds] => mupdbinds" ("_,/ _")
  "_MUpdate"  :: "['a, mupdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

translations
  "_MUpdate f (_mupdbinds b bs)" == "_MUpdate (_MUpdate f b) bs"
  "f(x:=\<^sub>my)" == "CONST fmap_upd f x y"


instantiation fmap :: (linorder,linorder) order
begin

definition less_eq_fmap :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool" where
"less_eq_fmap m1 m2 \<longleftrightarrow> fdom m1 |\<subseteq>| fdom m2 \<and> (\<forall>x|\<in>|fdom m1. the (\<langle>m1\<rangle>\<^sub>m x) \<le> the (\<langle>m2\<rangle>\<^sub>m x))"

definition less_fmap :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool" where
"less_fmap x y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"

instance 
  apply (intro_classes)
  apply (force simp add:less_fmap_def less_eq_fmap_def)
  apply (force simp add:less_fmap_def less_eq_fmap_def)
  apply (auto elim!:fsubset_elim fBall_elim intro!:fsubset_intro simp add:less_fmap_def less_eq_fmap_def fdom.rep_eq)
  apply (metis contra_subsetD domI option.sel order.trans)
  apply (metis eq_iff fdom.rep_eq fdomIff fmember.rep_eq fmext not_None_eq option.sel)
done
end

lemma fdom_less_eq [simp]:
  "m1 \<le> m2 \<Longrightarrow> fdom m1 |\<subseteq>| fdom m2"
  by (simp add:less_eq_fmap_def)

lemma fmap_values_less_eq [simp]:
  "\<lbrakk> m1 \<le> m2; x |\<in>| fdom m1 \<rbrakk> \<Longrightarrow> the (\<langle>m1\<rangle>\<^sub>m x) \<le> the (\<langle>m2\<rangle>\<^sub>m x)"
  by (auto simp add:less_eq_fmap_def)

lemma fmempty_least [simp]:
  "fmempty \<le> x"
  by (simp add:less_eq_fmap_def fdom.rep_eq zero_fmap.rep_eq)

lemma fmap_upd_less [intro]:
  "k |\<notin>| fdom f \<Longrightarrow> f \<le> fmap_upd f k v"
  apply (unfold less_eq_fmap_def)
  apply (auto)
  apply (metis fmap_upd.rep_eq fun_upd_apply option.distinct(1))
  apply (metis fmap_upd.rep_eq fun_upd_apply option.distinct(1) option.sel order_refl)
done

lemma fmap_fset_fmempty [simp]:
  "fmap_graph(0) = \<lbrace>\<rbrace>"
  by (auto intro:fmember_intro elim:fmember_elim simp add: fmap_graph.rep_eq zero_fmap.rep_eq map_graph_def)

lemma fdom_map_upd [simp]: 
  "fdom (f(k :=\<^sub>m Some v)) = finsert k (fdom f)"
  by (auto simp add:fdom.rep_eq fmap_upd.rep_eq)

lemma fmap_graph_upd [simp]:
  "k |\<notin>| fdom f \<Longrightarrow> fmap_graph (fmap_upd f k (Some v)) = finsert (k, v) (fmap_graph f)"
  apply (rule)
  apply (auto elim!:fmember_elim fnmember_elim intro!:fmember_intro simp add: finsert.rep_eq fmap_graph.rep_eq fmap_upd.rep_eq fdom.rep_eq dom_def map_graph_def)
  apply (metis)
  apply (metis option.inject)
done

lemma fmap_upd_apply [simp]: "\<langle>f(x:=\<^sub>my)\<rangle>\<^sub>m z = (if z=x then y else \<langle>f\<rangle>\<^sub>m z)"
  by (simp add:fmap_upd.rep_eq)

lemma fmap_upd_upd [simp]: "f(x:=\<^sub>my,x:=\<^sub>mz) = f(x:=\<^sub>mz)"
  by (auto)

lemma fempty_upd_None [simp]: "0(x:=\<^sub>mNone) = 0"
  by (auto simp add:zero_fmap.rep_eq)

lemma fupd_None_fran_subset:
  "fran(m(k:=\<^sub>mNone)) |\<subseteq>| fran(m)"
  apply (auto intro!:fmember_intro elim!:fmember_elim simp add:fran.rep_eq fmap_upd.rep_eq)
  apply (metis (hide_lams, mono_tags) ranI ran_restrictD restrict_complement_singleton_eq)
done

lemma fran_fmap_upd [simp]:
  "fran(m(k:=\<^sub>mSome v)) = \<lbrace>v\<rbrace> |\<union>| fran(m(k:=\<^sub>mNone))"
  apply (auto elim!:fmember_elim fnmember_elim intro!:fmember_intro simp add:fran.rep_eq fmap_upd.rep_eq)
  apply (metis fun_upd_same fun_upd_upd insert_iff ran_map_upd)
  apply (metis fun_upd_same ranI)
  apply (metis fun_upd_same fun_upd_upd insertCI ran_map_upd)
done

lemma fmap_add_comm: "fdom(m1) |\<inter>| fdom(m2) = \<lbrace>\<rbrace> \<Longrightarrow> m1 + m2 = m2 + m1"
  apply (erule fset_elim)
  apply (rule Rep_fmap_intro)
  apply (simp add:fdom.rep_eq fran.rep_eq plus_fmap.rep_eq)
  apply (metis map_add_comm)
done

text {* Composition of finite maps *}

lift_definition fmap_comp :: "('b, 'c) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap"
is "map_comp" 
  apply (auto simp add:fmaps_def)
  apply (metis finite_subset map_comp_dom)
done

lemma fmap_comp_0_0 [simp]: 
  "fmap_comp 0 f = 0"
  by (auto simp add:fmap_comp.rep_eq zero_fmap.rep_eq)
  
lemma fmap_comp_0_1 [simp]: 
  "fmap_comp f 0 = 0"
  by (auto simp add:fmap_comp.rep_eq zero_fmap.rep_eq)

lemma finite_dom_graph_map:
  "finite A \<Longrightarrow> finite (dom (graph_map A))"
  by (simp add:graph_map_def dom_def)

lift_definition fgraph_fmap :: "('a * 'b) fset \<Rightarrow> ('a, 'b) fmap" is graph_map
  by (simp add:fmaps_def, metis finite_dom_graph_map)

lift_definition fmap_collect :: "('a \<Rightarrow> 'b * 'c) \<Rightarrow> 'a fset \<Rightarrow> ('b, 'c) fmap"
is "\<lambda> f A. graph_map (f ` A)"
  by (auto simp add:fmaps_def, metis finite_dom_graph_map finite_imageI)

text {* Domain restriction *}

lift_definition fmap_domr :: "'a fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" 
is "\<lambda> s f. restrict_map f s" by (simp add:fmaps_def)

definition fmap_inj :: "('a, 'b) fmap \<Rightarrow> bool"
where "fmap_inj f = inj_on \<langle>f\<rangle>\<^sub>m (dom(\<langle>f\<rangle>\<^sub>m))"

lemma fmap_inj_empty: "fmap_inj(fmempty)"
  by (simp add:fmap_inj_def zero_fmap.rep_eq)

text {* Range restriction *}

lift_definition fmap_ranr :: "'b fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" 
  is "\<lambda> A f. ran_restrict_map f A" by (auto simp add:fmaps_def)

lift_definition fmap_inv :: "('a, 'b) fmap \<Rightarrow> ('b, 'a) fmap" 
is "map_inv" by (simp add:fmaps_def)

definition fmap_domr' :: "'a fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" where
"fmap_domr' s f = fmap_domr (fdom f -\<^sub>f s) f"

definition fmap_ranr' :: "'b fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" where
"fmap_ranr' s f = fmap_ranr (fran f -\<^sub>f s) f"

lemma finite_dom_map_of:
  fixes f :: "('a::linorder \<rightharpoonup> 'b)"
  assumes "finite (dom f)" 
  shows "\<exists> xs. f = map_of xs"
  by (metis Abs_fmap_inv assms fmap_list_inv list_fmap.rep_eq)

subsection {* Countability *}

definition to_nat_fmap :: "('a :: {countable, linorder}, 'b :: countable) fmap \<Rightarrow> nat" where
"to_nat_fmap m = to_nat (fmap_list m)"

lemma to_nat_fmap_inj: "inj to_nat_fmap"
  by (rule injI, simp add: to_nat_fmap_def, metis fmap_list_inv)

instance fmap :: ("{countable, linorder}", countable) countable
  apply (intro_classes)
  using to_nat_fmap_inj apply blast
done

definition finmaps :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) fmap set" where
"finmaps A B = {f. dom \<langle>f\<rangle>\<^sub>m \<subseteq> A \<and> ran \<langle>f\<rangle>\<^sub>m \<subseteq> B}"

lemma fmap_graph_inv [simp]: "fgraph_fmap (fmap_graph f) = f"
  by (transfer, simp)

lemma fmap_graph_inj:
  "inj fmap_graph"
  by (metis fmap_graph_inv inj_on_def)

lemma fmap_graph_Fow: "fmap_graph ` finmaps A B \<subseteq> Fow (A \<times> B)"
  apply (auto simp add: fmap_graph.rep_eq maps_def)
  apply (metis (no_types, lifting) contra_subsetD domIff fdomI fdomIff finmaps_def map_graph_mem_equiv mem_Collect_eq)
  apply (metis (no_types, lifting) Range.intros contra_subsetD finmaps_def mem_Collect_eq ran_map_graph)
done

lemma countable_finmaps: 
  fixes A :: "'a set" and B :: "'b set"
  assumes "countable A" "countable B"
  shows "countable (finmaps A B)"
proof -
  from assms obtain to_nat_graph :: "('a * 'b) fset \<Rightarrow> nat" where "inj_on to_nat_graph (Fow (A \<times> B))"
    by (meson countable_Fow countable_SIGMA inj_on_to_nat_on)
  hence "inj_on (to_nat_graph \<circ> fmap_graph) (finmaps A B)"
    apply (rule_tac comp_inj_on)
    apply (metis fmap_graph_inv inj_on_def)
    apply (simp add: fmap_graph_Fow subset_inj_on)
  done
  thus ?thesis
    using countable_def by blast
qed

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

lift_definition map_fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('d, 'a) fmap \<Rightarrow> ('d, 'b) fmap"
is "\<lambda> f m x. Option.bind (m x) (Some \<circ> f)" 
  by (simp add: fmaps_def, metis (no_types, lifting) bind_eq_None_conv domIff finite_subset subsetI)

lift_definition set_fmap :: "('d, 'a) fmap \<Rightarrow> 'a set" is ran .

lift_definition rel_fmap :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('d, 'a) fmap \<Rightarrow> ('d, 'b) fmap \<Rightarrow> bool"
is "\<lambda> R m1 m2. (dom(m1) = dom(m2) \<and> (\<forall> x \<in> dom(m1). R (the (m1 x)) (the (m2 x))))" .

bnf "('d, 'a) fmap"
  map: map_fmap
  sets: set_fmap
  bd: "natLeq +c |UNIV :: 'd set|"
  wits: fmempty
  rel: rel_fmap
proof -
  show "map_fmap id = id"
    by (auto simp add: map_fmap_def map_fun_def)
  show "\<And>f g. map_fmap (g \<circ> f) = map_fmap g \<circ> map_fmap f"    
    by (auto simp add: comp_def map_fmap.rep_eq)
  show "\<And>x f g. (\<And>z. z \<in> set_fmap x \<Longrightarrow> f z = g z) \<Longrightarrow> map_fmap f x = map_fmap g x"
    by (transfer, rule ext, simp add: ran_def, metis (mono_tags, lifting) Option.bind_cong comp_apply)
  show "\<And>f. set_fmap \<circ> map_fmap f = op ` f \<circ> set_fmap"
    by (auto simp add: comp_def set_fmap_def map_fmap.rep_eq ran_def)
  show "card_order (natLeq +c |UNIV| )"
    by (simp add: card_of_card_order_on card_order_csum natLeq_card_order)
  show "cinfinite (natLeq +c |UNIV| )"
    by (simp add: cinfinite_csum natLeq_cinfinite)
  show "\<And>x::('d, 'a) fmap. |set_fmap x| \<le>o natLeq +c |UNIV :: 'd set|"
  proof -
    fix F :: "('d, 'a) fmap"
    have "|set_fmap F| \<le>o |UNIV :: 'd set|" (is "_ \<le>o ?U")
    proof (transfer)
      fix F :: "'d \<rightharpoonup> 'a"
      assume "F \<in> fmaps"
      have "the ` F ` dom F = ran F"
        by (simp add: dom_image_ran)
      moreover have "|the ` F ` dom F| \<le>o |F ` dom F|"
        by (auto intro: card_of_image)
      moreover have "|F ` dom F| \<le>o |dom F|"
        by (auto intro: card_of_image)
      moreover have "|dom F| \<le>o |UNIV :: 'd set|"
         by (simp add: card_of_mono1)
      ultimately show "|ran F| \<le>o |UNIV :: 'd set|"
        by (auto intro: ordLeq_transitive card_of_image card_of_mono1)
    qed
    also have "?U \<le>o natLeq +c ?U"
      by (simp add: card_of_Card_order ordLeq_csum2)
    finally show "|set_fmap F| \<le>o natLeq +c |UNIV :: 'd set|" .
  qed
  show "\<And>R S. rel_fmap R OO rel_fmap S \<le> rel_fmap (R OO S)"
    apply (rule, transfer)
    apply (auto)
    apply blast+
    apply (metis domI option.sel relcompp.relcompI)
  done
  show "\<And> R :: 'a \<Rightarrow> 'b \<Rightarrow> bool. rel_fmap R =
         (BNF_Def.Grp {x::('d, 'a \<times> 'b) fmap. set_fmap x \<subseteq> {(x, y). R x y}} (map_fmap fst))\<inverse>\<inverse> OO BNF_Def.Grp {x. set_fmap x \<subseteq> {(x, y). R x y}} (map_fmap snd)"
         unfolding Grp_def fun_eq_iff relcompp.simps conversep.simps
         apply transfer
         unfolding rel_fun_def subset_iff image_iff
         apply auto
         apply (rule_tac x="[v \<mapsto> (the (x v), the (xa v)) | v. v \<in> dom x]" in bexI)
         apply (auto)
         apply (rule ext)
         apply (auto)
         apply (metis domI domIff option.collapse)
         apply (rule ext)
         apply (auto)
         apply (simp add: fmaps_def)
         apply (simp add: ranI)
  done
  show "\<And>z. z \<in> set_fmap fmempty \<Longrightarrow> False"
    by (transfer, auto)
qed
    
datatype mt = MyType string string "(string, mt) fmap"

end